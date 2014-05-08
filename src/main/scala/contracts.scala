package faba.contracts

import org.objectweb.asm.{Handle, Opcodes, Type}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.analysis.{BasicValue, BasicInterpreter, Frame}
import org.objectweb.asm.tree._

import faba.analysis._
import faba.cfg._
import faba.data._
import faba.engine._
import scala.Some

object `package` {
  type Value = Values.Value
}

case class ParamValue(tp: Type) extends BasicValue(tp)
case class InstanceOfCheckValue() extends BasicValue(Type.INT_TYPE)
case class TrueValue() extends BasicValue(Type.INT_TYPE)
case class FalseValue() extends BasicValue(Type.INT_TYPE)
case class NullValue() extends BasicValue(Type.getObjectType("null"))
case class NotNullValue(tp: Type) extends BasicValue(tp)
case class CallResultValue(tp: Type, parameter: AKey) extends BasicValue(tp)

case class Configuration(insnIndex: Int, frame: Frame[BasicValue])

case class PendingState(index: Int,
                        conf: Configuration,
                        history: List[Configuration],
                        pathTaken: Boolean) extends AState[Configuration] {

  import Utils._
  def isInstanceOf(prevState: PendingState) = {
    val result = pathTaken == prevState.pathTaken &&
      isInstance(conf, prevState.conf) &&
      history.size == prevState.history.size &&
      (history, prevState.history).zipped.forall(isInstance)
    result
  }

  override val stateIndex: Int = index
  override val insnIndex: Int = conf.insnIndex
}

sealed trait PendingAction
case class ProceedState(state: PendingState) extends PendingAction
case class MakeResult(state: PendingState, subIndices: List[Int]) extends PendingAction
sealed trait Result
case object Identity extends Result
case class SolutionWrapper(pathTaken: Boolean, sol: Dependence) extends Result

// TODO - migrate to Partial
case class Dependence(partial: Option[Value], params: Set[AKey])

object Result {
  def meet(r1: Result, r2: Result): Result = {
    val result = (r1, r2) match {
      case (Identity, _) => r2
      case (_, Identity) => r1
      case (SolutionWrapper(nt1, Dependence(p1, params1)), SolutionWrapper(nt2, Dependence(p2, params2))) =>
        val pathTaken = nt1 || nt2
        val partial: Option[Value] = (p1, p2) match {
          case (None, _) => p2
          case (_, None) => p1
          case (Some(ps1), Some(ps2)) if ps1 == ps2 =>
            Some(ps1)
          case _ => Some(Values.Top)
        }
        val params: Set[AKey] = partial match {
          case Some(Values.Top) => Set()
          case _ => params1 ++ params2
        }
        SolutionWrapper(pathTaken, Dependence(partial, params))
    }
    result
  }
}

// only null, not nulls are supported as in for now
class InOutAnalysis(val richControlFlow: RichControlFlow,
                    val paramIndex: Int,
                    val in: Value) extends Analysis[AKey, Value, Configuration, PendingState, Result] {
  import Utils._

  override val identity: Result = Identity
  private val methodNode =
    controlFlow.methodNode
  private val method = Method(controlFlow.className, methodNode.name, methodNode.desc)
  private val aKey = AKey(method, InOut(paramIndex, Values.Null))
  val interpreter = InOutInterpreter(Values.Null)

  override def stateInstance(curr: PendingState, prev: PendingState): Boolean =
    curr.isInstanceOf(prev)

  override def confInstance(curr: Configuration, prev: Configuration): Boolean =
    isInstance(curr, prev)

  override def createStartState(): PendingState =
    PendingState(0, Configuration(0, createStartFrame()), Nil, false)

  override def combineResults(delta: Result, subResults: List[Result]): Result =
    subResults.reduce(Result.meet)

  override def mkEquation(result: Result): Equation[AKey, Value] = result match {
    case Identity =>
      Equation(aKey, Final(Values.Top))
    case SolutionWrapper(false, _) =>
      Equation(aKey, Final(Values.Top))
    case SolutionWrapper(true, sol) if sol.params.isEmpty =>
      Equation(aKey, Final(sol.partial.getOrElse(Values.Top)))
    case SolutionWrapper(true, sol) =>
      Equation(aKey, Pending[AKey, Value](sol.partial.getOrElse(Values.Bot), sol.params.map(p => Component(false, Set(p)))))
  }

  var id = 0

  override def processState(state: PendingState): Unit = {
    val stateIndex = state.index
    val preConf = state.conf
    val insnIndex = preConf.insnIndex
    val loopEnter = dfsTree.loopEnters(insnIndex)
    val conf: Configuration =
      if (loopEnter) generalize(preConf) else preConf
    val history = state.history
    val pathTaken = state.pathTaken
    val frame = conf.frame
    val insnNode = methodNode.instructions.get(insnIndex)
    val nextHistory = if (loopEnter) conf :: history else history
    val nextFrame = execute(frame, insnNode)
    // early return
    insnNode.getOpcode match {
      case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
        popValue(frame) match {
          case FalseValue() =>
            val solution: SolutionWrapper = SolutionWrapper(pathTaken, Dependence(Some(Values.False), Set()))
            results = results + (stateIndex -> solution)
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case TrueValue() =>
            val solution: SolutionWrapper = SolutionWrapper(pathTaken, Dependence(Some(Values.True), Set()))
            results = results + (stateIndex -> solution)
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case CallResultValue(_, param) =>
            val solution: SolutionWrapper = SolutionWrapper(pathTaken, Dependence(None, Set(param)))
            results = results + (stateIndex -> solution)
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case NullValue() =>
            val solution: SolutionWrapper = SolutionWrapper(pathTaken, Dependence(Some(Values.Null), Set()))
            results = results + (stateIndex -> solution)
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case NotNullValue(_) =>
            val solution: SolutionWrapper = SolutionWrapper(pathTaken, Dependence(Some(Values.NotNull), Set()))
            results = results + (stateIndex -> solution)
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case ParamValue(_) =>
            val solution: SolutionWrapper = SolutionWrapper(pathTaken, Dependence(Some(in), Set()))
            results = results + (stateIndex -> solution)
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case _ =>
            val solution: SolutionWrapper = SolutionWrapper(pathTaken, Dependence(Some(Values.Top), Set()))
            results = results + (stateIndex -> solution)
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
        }
      case ATHROW =>
        results = results + (stateIndex -> SolutionWrapper(pathTaken, Dependence(Some(Values.Top), Set())))
        computed = computed.updated(insnIndex, state :: computed(insnIndex))
      case IFNONNULL if popValue(frame).isInstanceOf[ParamValue] =>
        val nextInsnIndex = in match {
          case Values.Null =>
            insnIndex + 1
          case Values.NotNull =>
            methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
        }
        val nextState = PendingState({
          id += 1; id
        }, Configuration(nextInsnIndex, nextFrame), nextHistory, true)
        pending.push(MakeResult(state, Identity, List(nextState.index)))
        pending.push(ProceedState(nextState))
      case IFNULL if popValue(frame).isInstanceOf[ParamValue] =>
        val nextInsnIndex = in match {
          case Values.Null =>
            methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          case Values.NotNull =>
            insnIndex + 1
        }
        val nextState = PendingState({
          id += 1; id
        }, Configuration(nextInsnIndex, nextFrame), nextHistory, true)
        pending.push(MakeResult(state, Identity, List(nextState.index)))
        pending.push(ProceedState(nextState))
      case IFEQ if popValue(frame).isInstanceOf[InstanceOfCheckValue] && in == Values.Null =>
        val nextInsnIndex =
          methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
        val nextState = PendingState({
          id += 1; id
        }, Configuration(nextInsnIndex, nextFrame), nextHistory, true)
        pending.push(MakeResult(state, Identity, List(nextState.index)))
        pending.push(ProceedState(nextState))
      case IFNE if popValue(frame).isInstanceOf[InstanceOfCheckValue] && in == Values.Null =>
        val nextInsnIndex = insnIndex + 1
        val nextState = PendingState({
          id += 1; id
        }, Configuration(nextInsnIndex, nextFrame), nextHistory, true)
        pending.push(MakeResult(state, Identity, List(nextState.index)))
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
            PendingState({
              id += 1; id
            }, Configuration(nextInsnIndex, nextFrame1), nextHistory, pathTaken)
        }
        pending.push(MakeResult(state, Identity, nextStates.map(_.index)))
        pending.pushAll(nextStates.map(s => ProceedState(s)))
    }
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

  private def execute(frame: Frame[BasicValue], insnNode: AbstractInsnNode) = insnNode.getType match {
    case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
      frame
    case _ =>
      val nextFrame = new Frame(frame)
      nextFrame.execute(insnNode, interpreter)
      nextFrame
  }

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
      case NullValue() =>
        frame.setLocal(i, BasicValue.UNINITIALIZED_VALUE)
      case NotNullValue(tp) =>
        frame.setLocal(i, new BasicValue(tp))
      case _ =>
    }

    val stack = (0 until frame.getStackSize).map(frame.getStack)
    frame.clearStack()

    // pushing back
    for (v <- stack) v match {
      case CallResultValue(tp, _) =>
        frame.push(new BasicValue(tp))
      case TrueValue() =>
        frame.push(BasicValue.INT_VALUE)
      case FalseValue() =>
        frame.push(BasicValue.INT_VALUE)
      case NullValue() =>
        frame.push(BasicValue.UNINITIALIZED_VALUE)
      case NotNullValue(tp) =>
        frame.push(new BasicValue(tp))
      case _ =>
        frame.push(v)
    }
    configuration
  }
}

object Utils {
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
    case (_: ParamValue) => curr match {
      case _: ParamValue => true
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
    case _: BasicValue => true
  }

  def popValue(frame: Frame[BasicValue]): BasicValue =
    frame.getStack(frame.getStackSize - 1)
}


case class InOutInterpreter(inValue: Value) extends BasicInterpreter {

  override def newOperation(insn: AbstractInsnNode): BasicValue =
    insn.getOpcode match {
      case ICONST_0 =>
        FalseValue()
      case ICONST_1 =>
        TrueValue()
      case ACONST_NULL =>
        NullValue()
      case LDC =>
        val cst = insn.asInstanceOf[LdcInsnNode].cst
        cst match {
          case tp: Type if tp.getSort == Type.OBJECT || tp.getSort == Type.ARRAY =>
            NotNullValue(Type.getObjectType("java/lang/Class"))
          case tp: Type if tp.getSort == Type.METHOD  =>
            NotNullValue(Type.getObjectType("java/lang/invoke/MethodType"))
          case s: String =>
            NotNullValue(Type.getObjectType("java/lang/String"))
          case h: Handle =>
            NotNullValue(Type.getObjectType("java/lang/invoke/MethodHandle"))
          case _ =>
            super.newOperation(insn)
        }
      case NEW =>
        NotNullValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc))
      case _ =>
        super.newOperation(insn)
    }

  override def unaryOperation(insn: AbstractInsnNode, value: BasicValue): BasicValue =
    insn.getOpcode match {
      case CHECKCAST if value.isInstanceOf[ParamValue] =>
        new ParamValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc))
      case INSTANCEOF if value.isInstanceOf[ParamValue] =>
        InstanceOfCheckValue()
      case NEWARRAY | ANEWARRAY =>
        NotNullValue(super.unaryOperation(insn, value).getType)
      case _ =>
        super.unaryOperation(insn, value)
    }


  // TODO - here only the first param is taken into account (for simplicity)
  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    val static = opCode == INVOKESTATIC
    val shift = if (static) 0 else 1
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL =>
        val mNode = insn.asInstanceOf[MethodInsnNode]
        for (i <- shift until values.size()) {
          if (values.get(i).isInstanceOf[ParamValue]) {
            val method = Method(mNode.owner, mNode.name, mNode.desc)
            return CallResultValue(
              Type.getReturnType(insn.asInstanceOf[MethodInsnNode].desc),
              AKey(method, InOut(i - shift, inValue))
            )
          }
        }
        super.naryOperation(insn, values)
      case MULTIANEWARRAY | INVOKEDYNAMIC =>
        NotNullValue(super.naryOperation(insn, values).getType)
      case _ =>
        super.naryOperation(insn, values)
    }
  }
}
