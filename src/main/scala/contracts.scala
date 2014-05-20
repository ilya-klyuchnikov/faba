package faba.contracts

import org.objectweb.asm.{Handle, Type}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.analysis.{BasicValue, BasicInterpreter, Frame}
import org.objectweb.asm.tree._

import faba.analysis._
import faba.cfg._
import faba.data._
import faba.engine._

class InOutAnalysis(val richControlFlow: RichControlFlow, val direction: Direction) extends Analysis[Result[Key, Value]] {
  type MyResult = Result[Key, Value]
  import Utils._

  override val identity = Final(Values.Bot)

  private val interpreter = InOutInterpreter(direction)
  private val optIn: Option[Value] = direction match {
    case InOut(_, in) => Some(in)
    case _ => None
  }

  override def stateInstance(curr: State, prev: State): Boolean = {
    curr.taken == prev.taken &&
      Utils.isInstance(curr.conf, prev.conf) &&
      curr.history.size == prev.history.size &&
      (curr.history, prev.history).zipped.forall(Utils.isInstance)
  }

  override def confInstance(curr: Conf, prev: Conf): Boolean =
    isInstance(curr, prev)

  override def combineResults(delta: MyResult, subResults: List[MyResult]): MyResult =
    subResults.reduce(_ join _)
  override def mkEquation(result: MyResult): Equation[Key, Value] =
      Equation(aKey, result)
  override def isEarlyResult(res: MyResult): Boolean = res match {
    case Final(Values.Top)      => true
    case Pending(Values.Top, _) => true
    case _                      => false
  }

  var id = 0

  override def processState(state: State): Unit = {
    val stateIndex = state.index
    val preConf = state.conf
    val insnIndex = preConf.insnIndex
    val loopEnter = dfsTree.loopEnters(insnIndex)
    val conf = if (loopEnter) generalize(preConf) else preConf
    val history = state.history
    val taken = state.taken
    val frame = conf.frame
    val insnNode = methodNode.instructions.get(insnIndex)
    val nextHistory = if (loopEnter) conf :: history else history
    val nextFrame = execute(frame, insnNode)

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
            results = results + (stateIndex -> Pending[Key, Value](Values.Bot, Set(Component(false, keys))))
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          case _ =>
            earlyResult = Some(Final(Values.Top))
        }
      case ATHROW =>
        earlyResult = Some(Final(Values.Top))
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

}

case class InOutInterpreter(direction: Direction) extends BasicInterpreter {

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
        val retType = Type.getReturnType(mNode.desc)
        val isRefRetType = retType.getSort == Type.OBJECT || retType.getSort == Type.ARRAY
        direction match {
          case InOut(_, inValue) =>
            var keys = Set[Key]()
            for (i <- shift until values.size()) {
              if (values.get(i).isInstanceOf[ParamValue])
                keys = keys + Key(method, InOut(i - shift, inValue))
            }
            if (isRefRetType)
              keys = keys + Key(method, Out)
            if (keys.nonEmpty)
              return CallResultValue(Type.getReturnType(mNode.desc), keys)
          case _ =>
            if (isRefRetType)
              return CallResultValue(Type.getReturnType(mNode.desc), Set(Key(method, Out)))
        }
        super.naryOperation(insn, values)
      case MULTIANEWARRAY | INVOKEDYNAMIC =>
        NotNullValue(super.naryOperation(insn, values).getType)
      case _ =>
        super.naryOperation(insn, values)
    }
  }
}
