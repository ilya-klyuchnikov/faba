package faba.contracts

import org.objectweb.asm.{Handle, Opcodes, Type}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.analysis.{BasicValue, BasicInterpreter, Frame}
import org.objectweb.asm.tree._

import faba.analysis._
import faba.cfg._
import faba.data._
import faba.engine._

case class ParamValue(tp: Type) extends BasicValue(tp)
case class InstanceOfCheckValue() extends BasicValue(Type.INT_TYPE)
case class TrueValue() extends BasicValue(Type.INT_TYPE)
case class FalseValue() extends BasicValue(Type.INT_TYPE)
case class NullValue() extends BasicValue(Type.getObjectType("null"))
case class NotNullValue(tp: Type) extends BasicValue(tp)
case class CallResultValue(tp: Type, inters: Set[AKey]) extends BasicValue(tp)

case class Conf(insnIndex: Int, frame: Frame[BasicValue])

case class State(index: Int, conf: Conf, history: List[Conf], taken: Boolean) extends AState[Conf] {

  def isInstanceOf(prevState: State) = {
    val result = taken == prevState.taken &&
      Utils.isInstance(conf, prevState.conf) &&
      history.size == prevState.history.size &&
      (history, prevState.history).zipped.forall(Utils.isInstance)
    result
  }

  override val stateIndex: Int = index
  override val insnIndex: Int = conf.insnIndex
}

sealed trait PendingAction
case class ProceedState(state: State) extends PendingAction
case class MakeResult(state: State, subIndices: List[Int]) extends PendingAction

class InOutAnalysis(val richControlFlow: RichControlFlow,
                    val direction: ADirection) extends Analysis[AKey, Value, Conf, State, Result[AKey, Value]] {
  type MyResult = Result[AKey, Value]
  import Utils._

  override val identity = Final(Values.Bot)

  private val methodNode = controlFlow.methodNode
  private val method = Method(controlFlow.className, methodNode.name, methodNode.desc)
  private val aKey = AKey(method, direction)

  private val interpreter = InOutInterpreter(direction)
  private val optIn: Option[Value] = direction match {
    case InOut(_, in) => Some(in)
    case _ => None
  }

  override def stateInstance(curr: State, prev: State): Boolean =
    curr.isInstanceOf(prev)
  override def confInstance(curr: Conf, prev: Conf): Boolean =
    isInstance(curr, prev)
  override def createStartState(): State =
    State(0, Conf(0, createStartFrame()), Nil, false)
  override def combineResults(delta: MyResult, subResults: List[MyResult]): MyResult =
    subResults.reduce(_ join _)
  override def mkEquation(result: MyResult): Equation[AKey, Value] =
      Equation(aKey, result)

  var id = 0

  override def processState(state: State): Unit = {
    val stateIndex = state.index
    val preConf = state.conf
    val insnIndex = preConf.insnIndex
    val loopEnter = dfsTree.loopEnters(insnIndex)
    val conf: Conf =
      if (loopEnter) generalize(preConf) else preConf
    val history = state.history
    val taken = state.taken
    val frame = conf.frame
    val insnNode = methodNode.instructions.get(insnIndex)
    val nextHistory = if (loopEnter) conf :: history else history
    val nextFrame = execute(frame, insnNode)
    // TODO early return
    insnNode.getOpcode match {
      case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
        popValue(frame) match {
          case FalseValue() =>
            results = results + (stateIndex -> Final(Values.False))
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case TrueValue() =>
            results = results + (stateIndex -> Final(Values.True))
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case NullValue() =>
            results = results + (stateIndex -> Final(Values.Null))
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case NotNullValue(_) =>
            results = results + (stateIndex -> Final(Values.NotNull))
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case ParamValue(_) =>
            val InOut(_, in) = direction
            results = results + (stateIndex -> Final(in))
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case CallResultValue(_, keys) =>
            results = results + (stateIndex -> Pending[AKey, Value](Values.Bot, Set(Component(false, keys))))
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case _ =>
            // TODO - may return Top right now
            results = results + (stateIndex -> Final(Values.Top))
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
        }
      case ATHROW =>
        // TODO - really, this may be Values.bot, discussable
        results = results + (stateIndex -> Final(Values.Top))
        computed = computed.updated(insnIndex, state :: computed(insnIndex))
      case IFNONNULL if popValue(frame).isInstanceOf[ParamValue] =>
        val nextInsnIndex = direction match {
          case InOut(_, Values.Null) =>
            insnIndex + 1
          case InOut(_, Values.NotNull) =>
            methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
        }
        val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true)
        pending.push(MakeResult(state, identity, List(nextState.index)))
        pending.push(ProceedState(nextState))
      case IFNULL if popValue(frame).isInstanceOf[ParamValue] =>
        val nextInsnIndex = direction match {
          case InOut(_, Values.Null) =>
            methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          case InOut(_, Values.NotNull) =>
            insnIndex + 1
        }
        val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true)
        pending.push(MakeResult(state, identity, List(nextState.index)))
        pending.push(ProceedState(nextState))
      case IFEQ if popValue(frame).isInstanceOf[InstanceOfCheckValue] && optIn == Some(Values.Null) =>
        val nextInsnIndex =
          methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
        val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true)
        pending.push(MakeResult(state, identity, List(nextState.index)))
        pending.push(ProceedState(nextState))
      case IFNE if popValue(frame).isInstanceOf[InstanceOfCheckValue] && optIn == Some(Values.Null) =>
        val nextInsnIndex = insnIndex + 1
        val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true)
        pending.push(MakeResult(state, identity, List(nextState.index)))
        pending.push(ProceedState(nextState))
      case IFEQ if popValue(frame).isInstanceOf[ParamValue] =>
        val nextInsnIndex = direction match {
          case InOut(_, Values.False) =>
            methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          case InOut(_, Values.True) =>
            insnIndex + 1
        }
        val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true)
        pending.push(MakeResult(state, identity, List(nextState.index)))
        pending.push(ProceedState(nextState))
      case IFNE if popValue(frame).isInstanceOf[ParamValue] =>
        val nextInsnIndex = direction match {
          case InOut(_, Values.False) =>
            insnIndex + 1
          case InOut(_, Values.True) =>
            methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
        }
        val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true)
        pending.push(MakeResult(state, identity, List(nextState.index)))
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
            State({id += 1; id}, Conf(nextInsnIndex, nextFrame1), nextHistory, taken)
        }
        pending.push(MakeResult(state, identity, nextStates.map(_.index)))
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
      val value = direction match {
        case InOut(`i`, _) =>
          new ParamValue(args(i))
        case _ =>
          new BasicValue(args(i))
      }
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

  def generalize(configuration: Conf): Conf = {
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
  def isInstance(curr: Conf, prev: Conf): Boolean = {
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
    case NullValue() => curr match {
      case NullValue() => true
      case _ => false
    }
    case NotNullValue(_) => curr match {
      case NotNullValue(_) => true
      case _ => false
    }
    case CallResultValue(_, prevInters) => curr match {
      case CallResultValue(_, currInters) => currInters == prevInters
      case _ => false
    }
    case _: BasicValue => true
  }

  def popValue(frame: Frame[BasicValue]): BasicValue =
    frame.getStack(frame.getStackSize - 1)
}

case class InOutInterpreter(direction: ADirection) extends BasicInterpreter {

  override def newOperation(insn: AbstractInsnNode): BasicValue =
    insn.getOpcode match {
      case ICONST_0 =>
        FalseValue()
      case ICONST_1 =>
        TrueValue()
      case ACONST_NULL =>
        NullValue()
      case LDC =>
        insn.asInstanceOf[LdcInsnNode].cst match {
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

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    val shift = if (opCode == INVOKESTATIC) 0 else 1
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL =>
        val mNode = insn.asInstanceOf[MethodInsnNode]
        val method = Method(mNode.owner, mNode.name, mNode.desc)
        direction match {
          case InOut(_, inValue) =>
            var keys = Set[AKey]()
            for (i <- shift until values.size()) {
              if (values.get(i).isInstanceOf[ParamValue])
                keys = keys + AKey(method, InOut(i - shift, inValue))
            }
            if (Type.getReturnType(mNode.desc).getSort == Type.OBJECT)
              keys = keys + AKey(method, Out)
            if (keys.nonEmpty)
              return CallResultValue(Type.getReturnType(mNode.desc), keys)
          case _ =>
            if (Type.getReturnType(mNode.desc).getSort == Type.OBJECT)
              return CallResultValue(Type.getReturnType(mNode.desc), Set(AKey(method, Out)))
        }
        super.naryOperation(insn, values)
      case MULTIANEWARRAY | INVOKEDYNAMIC =>
        NotNullValue(super.naryOperation(insn, values).getType)
      case _ =>
        super.naryOperation(insn, values)
    }
  }
}
