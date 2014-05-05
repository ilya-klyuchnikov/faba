package faba.analysis.notNullParams

import org.objectweb.asm.{Opcodes, Type}
import org.objectweb.asm.tree.analysis.{Frame, BasicValue}
import org.objectweb.asm.tree.{JumpInsnNode, AbstractInsnNode}
import org.objectweb.asm.Opcodes.{RETURN => VRETURN, _}
import scala.collection.mutable
import scala.collection.immutable.IntMap

import faba.analysis.RichControlFlow

class ParamValue(tp: Type) extends BasicValue(tp)
object InstanceOfCheckValue extends BasicValue(Type.INT_TYPE)

case class Parameter(className: String, methodName: String, methodDesc: String, arg: Int) {
  override def toString = s"$className $methodName$methodDesc #$arg"
}

sealed trait Result
case object Bottom extends Result
case object Return extends Result
case object NPE extends Result
case class ConditionalNPE(cnf: CNF) extends Result

object Result {
  def meet(r1: Result, r2: Result): Result = (r1, r2) match {
    case (Bottom, _) => r2
    case (_, Bottom) => r1
    case (Return, _) => Return
    case (_, Return) => Return
    case (NPE, NPE) => NPE
    case (NPE, r2:ConditionalNPE) => r2
    case (r1:ConditionalNPE, NPE) => r1
    case (ConditionalNPE(e1), ConditionalNPE(e2)) => ConditionalNPE(e1 meet e2)
  }

  def join(r1: Result, r2: Result): Result = (r1, r2) match {
    case (Bottom, _) => r2
    case (_, Bottom) => r1
    case (Return, _) => r2
    case (_, Return) => r1
    case (NPE, _) => NPE
    case (_, NPE) => r2
    case (ConditionalNPE(e1), ConditionalNPE(e2)) => ConditionalNPE(e1 join e2)
  }
}

case class Configuration(insnIndex: Int, frame: Frame[BasicValue])
case class PendingState(index: Int, conf: Configuration, history: List[Configuration], nullPathTaken: Boolean) {
  import Analyzer._
  def isInstanceOf(prevState: PendingState) =
    nullPathTaken == prevState.nullPathTaken &&
      isInstance(conf, prevState.conf) &&
      history.size == prevState.history.size &&
      (history, prevState.history).zipped.forall(isInstance)
}

sealed trait PendingAction
case class ProceedState(state: PendingState) extends PendingAction
case class MakeResult(state: PendingState, subResult: Result, subIndices: List[Int]) extends PendingAction

case class Analyzer(richControlFlow: RichControlFlow, paramIndex: Int) {
  import Analyzer._

  private val controlFlow = richControlFlow.controlFlow
  private val dfsTree = richControlFlow.dfsTree
  private val methodNode = controlFlow.methodNode
  private val parameter = Parameter(controlFlow.className, methodNode.name, methodNode.desc, paramIndex)

  def analyze(): Equation = {
    var id = 0

    val startState =
      PendingState(0, Configuration(0, createStartFrame()), Nil, false)
    val pending =
      mutable.Stack[PendingAction](ProceedState(startState))

    // the key is insnIndex
    var computed = IntMap[List[PendingState]]().withDefaultValue(Nil)
    // the key is stateIndex
    var results = IntMap[Result]()

    while (pending.nonEmpty) pending.pop() match {
      case MakeResult(state, delta, subIndices) =>
        val subResult = subIndices.map(results).reduce(Result.meet)
        val result = Result.join(delta, subResult)
        results = results + (state.index -> result)
        val insnIndex = state.conf.insnIndex
        computed = computed.updated(insnIndex, state :: computed(insnIndex))
      case ProceedState(state) =>

        val stateIndex = state.index
        val conf = state.conf
        val insnIndex = conf.insnIndex
        val history = state.history
        val nullPathTaken = state.nullPathTaken
        val frame = conf.frame

        val loopEnter = dfsTree.loopEnters(insnIndex)
        val loop = loopEnter && history.exists(prevConf => isInstance(conf, prevConf))

        if (loop) {
          results = results + (stateIndex -> Bottom)
          computed = computed.updated(insnIndex, state :: computed(insnIndex))
        } else computed(insnIndex).find(state.isInstanceOf(_)) match {
          case Some(ps) =>
            results = results + (stateIndex -> results(ps.index))
          case None =>
            // TODO - specialized code starts
            val insnNode = methodNode.instructions.get(insnIndex)
            val nextHistory = if (loopEnter) conf :: history else history
            val (nextFrame, subResult) = execute(frame, insnNode)
            // early return
            if (subResult == NPE) {
              results = results + (stateIndex -> NPE)
              computed = computed.updated(insnIndex, state :: computed(insnIndex))
            } else insnNode.getOpcode match {
              case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | VRETURN =>
                results = results + (stateIndex -> Return)
                computed = computed.updated(insnIndex, state :: computed(insnIndex))
              case ATHROW if nullPathTaken =>
                results = results + (stateIndex -> NPE)
                computed = computed.updated(insnIndex, state :: computed(insnIndex))
              case ATHROW =>
                results = results + (stateIndex -> Bottom)
                computed = computed.updated(insnIndex, state :: computed(insnIndex))
              case IFNONNULL if popValue(frame).isInstanceOf[ParamValue] =>
                val nextInsnIndex = insnIndex + 1
                val nextState = PendingState({id += 1; id}, Configuration(nextInsnIndex, nextFrame), nextHistory, true)
                pending.push(MakeResult(state, subResult, List(nextState.index)))
                pending.push(ProceedState(nextState))
              case IFNULL if popValue(frame).isInstanceOf[ParamValue] =>
                val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
                val nextState = PendingState({id += 1; id}, Configuration(nextInsnIndex, nextFrame), nextHistory, true)
                pending.push(MakeResult(state, subResult, List(nextState.index)))
                pending.push(ProceedState(nextState))
              case IFEQ if popValue(frame) == InstanceOfCheckValue =>
                val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
                val nextState = PendingState({id += 1; id}, Configuration(nextInsnIndex, nextFrame), nextHistory, true)
                pending.push(MakeResult(state, subResult, List(nextState.index)))
                pending.push(ProceedState(nextState))
              case IFNE if popValue(frame) == InstanceOfCheckValue =>
                val nextInsnIndex = insnIndex + 1
                val nextState = PendingState({id += 1; id}, Configuration(nextInsnIndex, nextFrame), nextHistory, true)
                pending.push(MakeResult(state, subResult, List(nextState.index)))
                pending.push(ProceedState(nextState))
              case _ =>
                val nextInsnIndices = controlFlow.transitions(insnIndex)
                val nextStates = nextInsnIndices.map {
                  nextInsnIndex =>
                    val nextFrame1 = if (controlFlow.errorTransitions(insnIndex -> nextInsnIndex)) {
                      val handler = new Frame(frame)
                      handler.clearStack()
                      handler.push(new BasicValue(Type.getType("java/lang/Throwable")))
                      handler
                    } else {
                      nextFrame
                    }
                    PendingState({id += 1; id}, Configuration(nextInsnIndex, nextFrame1), nextHistory, nullPathTaken)
                }
                pending.push(MakeResult(state, subResult, nextStates.map(_.index)))
                pending.pushAll(nextStates.map(s => ProceedState(s)))
            }
            // TODO - specialized code ends
        }
    }

    mkEquation(results(0))
  }

  private def mkEquation(result: Result) = result match {
    case Bottom | Return => Equation(parameter, Nullable)
    case NPE => Equation(parameter, NotNull)
    case ConditionalNPE(cnf) => Equation(parameter, Dependence(cnf))
  }

  private def execute(frame: Frame[BasicValue], insnNode: AbstractInsnNode) = insnNode.getType match {
      case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
        (frame, Bottom)
      case _ =>
        val nextFrame = new Frame(frame)
        Interpreter.reset()
        nextFrame.execute(insnNode, Interpreter)
        (nextFrame, Interpreter.getUsage.toResult)
    }

  private def createStartFrame(): Frame[BasicValue] = {
    val frame = new Frame[BasicValue](methodNode.maxLocals, methodNode.maxStack)
    val returnType = Type.getReturnType(methodNode.desc)
    val returnValue = if (returnType == Type.VOID_TYPE) null else new BasicValue(returnType)
    frame.setReturn(returnValue)

    val args = Type.getArgumentTypes(methodNode.desc)
    var local = 0
    if ((methodNode.access & Opcodes.ACC_STATIC) == 0) {
      val basicValue = new BasicValue(Type.getObjectType(controlFlow.className))
      frame.setLocal(local, basicValue)
      local += 1
    }
    for (i <- 0 until args.size) {
      val value = if (i == paramIndex) new ParamValue(args(i)) else new BasicValue(args(i))
      frame.setLocal(local, value)
      local += 1
      if (args(i).getSize == 2) {
        frame.setLocal(local, BasicValue.UNINITIALIZED_VALUE)
        local += 1
      }
    }
    while (local < methodNode.maxLocals) {
      frame.setLocal(local, BasicValue.UNINITIALIZED_VALUE)
      local += 1
    }
    frame
  }
}

object Analyzer {
  def isInstance(curr: Configuration, prev: Configuration): Boolean = {
    if (curr.insnIndex != prev.insnIndex) {
      return false
    }
    val currFr = curr.frame
    val prevFr = prev.frame
    for (i <- 0 until currFr.getLocals if !isInstance(currFr.getLocal(i), prevFr.getLocal(i)))
      return false
    for (i <- 0 until currFr.getStackSize if !isInstance(currFr.getStack(i), prevFr.getStack(i)))
      return false
    true
  }

  def isInstance(curr: BasicValue, prev: BasicValue): Boolean = prev match {
    case _:ParamValue =>
      curr.isInstanceOf[ParamValue]
    case InstanceOfCheckValue =>
      curr == InstanceOfCheckValue
    case _ =>
      true
  }

  def popValue(frame: Frame[BasicValue]): BasicValue =
    frame.getStack(frame.getStackSize - 1)
}
