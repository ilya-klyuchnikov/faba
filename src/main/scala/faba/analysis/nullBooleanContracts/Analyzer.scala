package faba.analysis.nullBooleanContracts

import org.objectweb.asm.{Opcodes, Type}
import org.objectweb.asm.tree.analysis.{Frame, BasicValue}
import org.objectweb.asm.tree.{JumpInsnNode, AbstractInsnNode}
import scala.collection.mutable
import scala.collection.immutable.IntMap
import org.objectweb.asm.Opcodes._
import faba.analysis.RichControlFlow

case class ParamValue(tp: Type) extends BasicValue(tp)
case class InstanceOfCheckValue() extends BasicValue(Type.INT_TYPE)
case class TrueValue() extends BasicValue(Type.INT_TYPE)
case class FalseValue() extends BasicValue(Type.INT_TYPE)
case class CallResultValue(tp: Type, parameter: Parameter) extends BasicValue(tp)

case class Parameter(className: String, methodName: String, methodDesc: String, arg: Int) {
  override def toString = s"$className $methodName$methodDesc #$arg"
}

case class Configuration(insnIndex: Int, frame: Frame[BasicValue])
case class PendingState(index: Int, conf: Configuration, history: List[Configuration], nullPathTaken: Boolean) {
  import Analyzer._
  def isInstanceOf(prevState: PendingState) = {
    val result = nullPathTaken == prevState.nullPathTaken &&
      isInstance(conf, prevState.conf) &&
      history.size == prevState.history.size &&
      (history, prevState.history).zipped.forall(isInstance)

    result
  }
}

sealed trait PendingAction
case class ProceedState(state: PendingState) extends PendingAction
case class MakeResult(state: PendingState, subIndices: List[Int]) extends PendingAction

sealed trait Result
case object Bottom extends Result
case class SolutionWrapper(nullTaken: Boolean, sol: Dependence) extends Result

object Result {
  def meet(r1: Result, r2: Result): Result = {
    val result =  (r1, r2) match {
      case (Bottom, _) => r2
      case (_, Bottom) => r1
      case (SolutionWrapper(nt1, Dependence(p1, params1)), SolutionWrapper(nt2, Dependence(p2, params2))) =>
        val nullTaken = nt1 || nt2
        val partial: Option[PartialSolution] = (p1, p2) match {
          case (None, _) => p2
          case (_, None) => p1
          case (Some(ps1), Some(ps2)) if ps1 == ps2 =>
            Some(ps1)
          case _ => Some(AnyComponent)
        }
        val params: Set[Parameter] = partial match {
          case Some(AnyComponent) => Set()
          case _ => params1 ++ params2
        }
        SolutionWrapper(nullTaken, Dependence(partial, params))
    }
    result
  }
}

case class Analyzer(richControlFlow: RichControlFlow, paramIndex: Int) {
  import Analyzer._

  private val controlFlow = richControlFlow.controlFlow
  private val dfsTree = richControlFlow.dfsTree
  private val methodNode = controlFlow.methodNode
  private val parameter = Parameter(controlFlow.className, methodNode.name, methodNode.desc, paramIndex)

  def generalize(configuration: Configuration): Configuration = {
    //println("generalizing")
    val frame = configuration.frame
    for (i <- 0 until frame.getLocals) frame.getLocal(i) match {
      case CallResultValue(tp, _) =>
        frame.setLocal(i, new BasicValue(tp))

      case TrueValue() =>
        frame.setLocal(i, BasicValue.INT_VALUE)
      case FalseValue() =>
        frame.setLocal(i, BasicValue.INT_VALUE)
      case _ =>
    }

    val stack = (0 until frame.getStackSize).map(frame.getStack)
    frame.clearStack()

    // pushing back
    for (v <- stack) v match {
      case CallResultValue(tp, _) =>
        frame.push(new BasicValue(tp))
      case _ =>
        frame.push(v)
    }
    configuration
  }


  def mkEquation(result: Result): Equation = result match {
    case Bottom =>
      Equation(parameter, Dependence(Some(AnyComponent), Set()))
    case SolutionWrapper(false, _) =>
      Equation(parameter, Dependence(Some(AnyComponent), Set()))
    case SolutionWrapper(true, sol) =>
      Equation(parameter, sol)
  }


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
      case MakeResult(state, subIndices) =>
        val result = subIndices.map(results).reduce(Result.meet)
        results = results + (state.index -> result)
        val insnIndex = state.conf.insnIndex
        computed = computed.updated(insnIndex, state :: computed(insnIndex))

      case ProceedState(state) =>
        val stateIndex = state.index
        val preConf = state.conf
        val insnIndex = preConf.insnIndex
        val loopEnter = dfsTree.loopEnters(insnIndex)

        // generalization
        val conf: Configuration =
          if (loopEnter) generalize(preConf) else preConf

        val history = state.history
        val nullPathTaken = state.nullPathTaken
        val frame = conf.frame
        val loop = loopEnter && history.exists(prevConf => isInstance(conf, prevConf))

        if (loop) {
          results = results + (stateIndex -> Bottom)
          computed = computed.updated(insnIndex, state :: computed(insnIndex))
        } else computed(insnIndex).find(state.isInstanceOf(_)) match {
          // to basic configuration
          case Some(ps) =>
            results = results + (stateIndex -> results(ps.index))

          case None =>
            // TODO - specialized code starts
            val insnNode = methodNode.instructions.get(insnIndex)
            val nextHistory = if (loopEnter) conf :: history else history
            val nextFrame = execute(frame, insnNode)
            // early return
            insnNode.getOpcode match {
              case IRETURN =>
                val returnValue = popValue(frame)
                returnValue match {
                  case FalseValue() =>
                    val solution: SolutionWrapper = SolutionWrapper(nullPathTaken, Dependence(Some(FalseComponent), Set()))
                    results = results + (stateIndex -> solution)
                    computed = computed.updated(insnIndex, state :: computed(insnIndex))
                  case TrueValue() =>
                    val solution: SolutionWrapper = SolutionWrapper(nullPathTaken, Dependence(Some(TrueComponent), Set()))
                    results = results + (stateIndex -> solution)
                    computed = computed.updated(insnIndex, state :: computed(insnIndex))
                  case CallResultValue(_, param) =>
                    val solution: SolutionWrapper = SolutionWrapper(nullPathTaken, Dependence(None, Set(param)))
                    results = results + (stateIndex -> solution)
                    computed = computed.updated(insnIndex, state :: computed(insnIndex))
                  case _ =>
                    val solution: SolutionWrapper = SolutionWrapper(nullPathTaken, Dependence(Some(AnyComponent), Set()))
                    results = results + (stateIndex -> solution)
                    computed = computed.updated(insnIndex, state :: computed(insnIndex))
                }
              case ATHROW =>
                results = results + (stateIndex -> SolutionWrapper(nullPathTaken, Dependence(Some(AnyComponent), Set())))
                computed = computed.updated(insnIndex, state :: computed(insnIndex))
              case IFNONNULL if popValue(frame).isInstanceOf[ParamValue] =>
                val nextInsnIndex = insnIndex + 1
                val nextState = PendingState({id += 1; id}, Configuration(nextInsnIndex, nextFrame), nextHistory, true)
                pending.push(MakeResult(state, List(nextState.index)))
                pending.push(ProceedState(nextState))
              case IFNULL if popValue(frame).isInstanceOf[ParamValue] =>
                val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
                val nextState = PendingState({id += 1; id}, Configuration(nextInsnIndex, nextFrame), nextHistory, true)
                pending.push(MakeResult(state, List(nextState.index)))
                pending.push(ProceedState(nextState))
              case IFEQ if popValue(frame).isInstanceOf[InstanceOfCheckValue]  =>
                val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
                val nextState = PendingState({id += 1; id}, Configuration(nextInsnIndex, nextFrame), nextHistory, true)
                pending.push(MakeResult(state, List(nextState.index)))
                pending.push(ProceedState(nextState))
              case IFNE if popValue(frame).isInstanceOf[InstanceOfCheckValue]  =>
                val nextInsnIndex = insnIndex + 1
                val nextState = PendingState({id += 1; id}, Configuration(nextInsnIndex, nextFrame), nextHistory, true)
                pending.push(MakeResult(state, List(nextState.index)))
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
                pending.push(MakeResult(state, nextStates.map(_.index)))
                pending.pushAll(nextStates.map(s => ProceedState(s)))
            }
            // TODO - specialized code ends
        }
    }

    mkEquation(results(0))
  }

  private def execute(frame: Frame[BasicValue], insnNode: AbstractInsnNode) = insnNode.getType match {
    case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
      frame
    case _ =>
      val nextFrame = new Frame(frame)
      nextFrame.execute(insnNode, Interpreter)
      nextFrame
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
    case (_:ParamValue) => curr match {
      case _:ParamValue => true
      case _ => false
    }
    case InstanceOfCheckValue() => curr match {
      case InstanceOfCheckValue() => true
      case _ => false
    }
    case TrueValue() => curr match {
      case TrueValue() => true
      case _ => false
    }
    case FalseValue() => curr match {
      case FalseValue() => true
      case _ => false
    }
    case CallResultValue(_, prevParam) => curr match {
      case CallResultValue(_, currParam) => currParam == prevParam
      case _ => false
    }
    case _:BasicValue => true
  }

  def popValue(frame: Frame[BasicValue]): BasicValue =
    frame.getStack(frame.getStackSize - 1)
}
