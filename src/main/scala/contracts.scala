package faba.contracts

import scala.annotation.switch

import org.objectweb.asm.{Handle, Type}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.analysis.{BasicValue, BasicInterpreter, Frame}
import org.objectweb.asm.tree._

import faba.analysis._
import faba.cfg._
import faba.data._
import faba.engine._

class InOutAnalysis(val richControlFlow: RichControlFlow, val direction: Direction, resultOrigins: Set[Int], val stable: Boolean) extends Analysis[Result[Key, Value]] {
  type MyResult = Result[Key, Value]
  implicit val contractsLattice = ELattice(Values.Bot, Values.Top)

  val propagateNullityTest_? = true
  override val identity = Final(Values.Bot)

  private val interpreter = InOutInterpreter(direction, methodNode.instructions, resultOrigins)
  private val optIn: Option[Value] = direction match {
    case InOut(_, in) => Some(in)
    case _ => None
  }

  override def combineResults(delta: MyResult, subResults: List[MyResult]): MyResult =
    subResults.reduce(_ join _)

  override def mkEquation(result: MyResult): Equation[Key, Value] =
    Equation(aKey, result)

  override def isEarlyResult(res: MyResult): Boolean = res match {
    case Final(Values.Top) => true
    case _                 => false
  }

  override def processState(fState: State): Unit = {


    var state = fState
    var states: List[State] = Nil

    while (true) {
      // sharing
      computed(state.conf.insnIndex).find(prevState => stateEquiv(state, prevState)) match {
        case Some(ps) =>
          results = results + (state.index -> results(ps.index))
          if (states.nonEmpty) pending.push(MakeResult(states, identity, List(ps.index)))
          return
        case None =>
      }

      val stateIndex = state.index
      val preConf = state.conf
      val insnIndex = preConf.insnIndex
      val loopEnter = dfsTree.loopEnters(insnIndex)
      val history = state.history

      val fold = loopEnter && history.exists(prevConf => confInstance(preConf, prevConf))

      if (fold) {
        results = results + (stateIndex -> identity)
        computed = computed.updated(insnIndex, state :: computed(insnIndex))
        if (states.nonEmpty) pending.push(MakeResult(states, identity, List(stateIndex)))
        return
      }

      val conf = if (loopEnter) generalize(preConf) else preConf

      val taken = state.taken
      val frame = conf.frame
      val insnNode = methodNode.instructions.get(insnIndex)
      val nextHistory = if (loopEnter) conf :: history else history
      val nextFrame = execute(frame, insnNode)
      val shared = richControlFlow.isSharedInstruction(insnIndex)

      if (interpreter.dereferenced) {
        results = results + (stateIndex -> Final(Values.Bot))
        if (shared)
          computed = computed.updated(insnIndex, state :: computed(insnIndex))
        if (states.nonEmpty) pending.push(MakeResult(states, identity, List(stateIndex)))
        return
      }

      insnNode.getOpcode match {
        case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
          popValue(frame) match {
            case FalseValue() =>
              results = results + (stateIndex -> Final(Values.False))
              if (shared)
                computed = computed.updated(insnIndex, state :: computed(insnIndex))
              if (states.nonEmpty) pending.push(MakeResult(states, identity, List(stateIndex)))
              return
            case TrueValue() =>
              results = results + (stateIndex -> Final(Values.True))
              if (shared)
                computed = computed.updated(insnIndex, state :: computed(insnIndex))
              if (states.nonEmpty) pending.push(MakeResult(states, identity, List(stateIndex)))
              return
            case NullValue() =>
              results = results + (stateIndex -> Final(Values.Null))
              if (shared)
                computed = computed.updated(insnIndex, state :: computed(insnIndex))
              if (states.nonEmpty) pending.push(MakeResult(states, identity, List(stateIndex)))
              return
            case NotNullValue(_) =>
              results = results + (stateIndex -> Final(Values.NotNull))
              if (shared)
                computed = computed.updated(insnIndex, state :: computed(insnIndex))
              if (states.nonEmpty) pending.push(MakeResult(states, identity, List(stateIndex)))
              return
            case ParamValue(_) =>
              val InOut(_, in) = direction
              results = results + (stateIndex -> Final(in))
              if (shared)
                computed = computed.updated(insnIndex, state :: computed(insnIndex))
              if (states.nonEmpty) pending.push(MakeResult(states, identity, List(stateIndex)))
              return
            case CallResultValue(_, keys) =>
              results = results + (stateIndex -> Pending[Key, Value](Set(Component(Values.Top, keys))))
              if (shared)
                computed = computed.updated(insnIndex, state :: computed(insnIndex))
              if (states.nonEmpty) pending.push(MakeResult(states, identity, List(stateIndex)))
              return
            case _ =>
              earlyResult = Some(Final(Values.Top))
              return
          }
        case ATHROW =>
          results = results + (stateIndex -> Final(Values.Bot))
          if (shared)
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          if (states.nonEmpty) pending.push(MakeResult(states, identity, List(stateIndex)))
          return
        case IFNONNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = (direction: @unchecked) match {
            case InOut(_, Values.Null) =>
              insnIndex + 1
            case InOut(_, Values.NotNull) =>
              methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          }
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
          states = state :: states
          state = nextState
        case IFNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = (direction: @unchecked) match {
            case InOut(_, Values.Null) =>
              methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
            case InOut(_, Values.NotNull) =>
              insnIndex + 1
          }
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
          states = state :: states
          state = nextState
        case IFEQ if popValue(frame).isInstanceOf[InstanceOfCheckValue] && optIn == Some(Values.Null) =>
          val nextInsnIndex =
            methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
          states = state :: states
          state = nextState
        case IFNE if popValue(frame).isInstanceOf[InstanceOfCheckValue] && optIn == Some(Values.Null) =>
          val nextInsnIndex = insnIndex + 1
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
          pending.push(MakeResult(List(state), identity, List(nextState.index)))
          state = nextState
        case IFEQ if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = (direction: @unchecked) match {
            case InOut(_, Values.False) =>
              methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
            case InOut(_, Values.True) =>
              insnIndex + 1
          }
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
          states = state :: states
          state = nextState
        case IFNE if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = (direction: @unchecked) match {
            case InOut(_, Values.False) =>
              insnIndex + 1
            case InOut(_, Values.True) =>
              methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          }
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
          states = state :: states
          state = nextState
        case IFNULL if propagateNullityTest_? && /*direction == Out &&*/ frame.mapping.head != -1  =>
          val nullInsn = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val notNullInsn = insnIndex + 1

          val nullFrame = new SmartFrame(nextFrame)
          nullFrame.setLocal(frame.mapping.head, NullValue())

          val notNullFrame = new SmartFrame(nextFrame)
          notNullFrame.setLocal(frame.mapping.head, NotNullValue(nextFrame.getLocal(frame.mapping.head).getType))

          val nullState = State(mkId(), Conf(nullInsn, nullFrame), nextHistory, taken, false)
          val notNullState = State(mkId(), Conf(notNullInsn, notNullFrame), nextHistory, taken, false)
          val nextStates = List(nullState, notNullState)
          states = state :: states
          pending.push(MakeResult(states, identity, nextStates.map(_.index)))
          pending.pushAll(nextStates.map(s => ProceedState(s)))
          return

        case IFNONNULL if propagateNullityTest_? && /*direction == Out &&*/ frame.mapping.head != -1  =>
          val notNullInsn = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nullInsn = insnIndex + 1

          val nullFrame = new SmartFrame(nextFrame)
          nullFrame.setLocal(frame.mapping.head, NullValue())

          val notNullFrame = new SmartFrame(nextFrame)
          notNullFrame.setLocal(frame.mapping.head, NotNullValue(nextFrame.getLocal(frame.mapping.head).getType))

          val nullState = State(mkId(), Conf(nullInsn, nullFrame), nextHistory, taken, false)
          val notNullState = State(mkId(), Conf(notNullInsn, notNullFrame), nextHistory, taken, false)
          val nextStates = List(nullState, notNullState)
          states = state :: states
          pending.push(MakeResult(states, identity, nextStates.map(_.index)))
          pending.pushAll(nextStates.map(s => ProceedState(s)))
          return
        case _ =>
          val nextInsnIndices = controlFlow.transitions(insnIndex)
          val nextStates = nextInsnIndices.map {
            nextInsnIndex =>
              val nextFrame1 = if (controlFlow.errorTransitions(insnIndex -> nextInsnIndex)) {
                val handler = new SmartFrame(frame)
                handler.clearStack()
                handler.push(new BasicValue(Type.getType("java/lang/Throwable")))
                handler
              } else {
                nextFrame
              }
              State(mkId(), Conf(nextInsnIndex, nextFrame1), nextHistory, taken, false)
          }
          states = state :: states
          if (nextStates.size == 1) {
            state = nextStates.head
          } else {
            pending.push(MakeResult(states, identity, nextStates.map(_.index)))
            pending.pushAll(nextStates.map(s => ProceedState(s)))
            return
          }
      }
    }
  }

  private def execute(frame: SmartFrame[BasicValue], insnNode: AbstractInsnNode): SmartFrame[BasicValue] = insnNode.getType match {
    case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
      interpreter.dereferenced = false
      frame
    case _ =>
      interpreter.dereferenced = false
      val nextFrame = new SmartFrame(frame)
      nextFrame.execute(insnNode, interpreter)
      nextFrame
  }

  // in-place generalization
  def generalize(conf: Conf): Conf = {
    val frame = new SmartFrame(conf.frame)
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
    Conf(conf.insnIndex, frame)
  }
}

case class InOutInterpreter(direction: Direction, insns: InsnList, resultOrigins: Set[Int]) extends BasicInterpreter {

  var dereferenced = false
  val nullAnalysis = direction match {
    case InOut(_, Values.Null) => true
    case _ => false
  }

  @inline
  def isResultOrigin(insn: AbstractInsnNode) =
    resultOrigins == null || resultOrigins(insns.indexOf(insn))

  @switch
  override def newOperation(insn: AbstractInsnNode): BasicValue = {
    val propagate_? = isResultOrigin(insn)
    insn.getOpcode match {
      case ICONST_0 if propagate_? =>
        FalseValue()
      case ICONST_1 if propagate_? =>
        TrueValue()
      case ACONST_NULL if propagate_? =>
        NullValue()
      case LDC if propagate_? =>
        insn.asInstanceOf[LdcInsnNode].cst match {
          case tp: Type if tp.getSort == Type.OBJECT || tp.getSort == Type.ARRAY =>
            NotNullValue(Type.getObjectType("java/lang/Class"))
          case tp: Type if tp.getSort == Type.METHOD =>
            NotNullValue(Type.getObjectType("java/lang/invoke/MethodType"))
          case s: String =>
            NotNullValue(Type.getObjectType("java/lang/String"))
          case h: Handle =>
            NotNullValue(Type.getObjectType("java/lang/invoke/MethodHandle"))
          case _ =>
            super.newOperation(insn)
        }
      case NEW if propagate_? =>
        NotNullValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc))
      case _ =>
        super.newOperation(insn)
    }
  }

  @switch
  override def unaryOperation(insn: AbstractInsnNode, value: BasicValue): BasicValue = {
    val propagate_? = isResultOrigin(insn)
    insn.getOpcode match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER if nullAnalysis && value.isInstanceOf[ParamValue] =>
        dereferenced = true
        super.unaryOperation(insn, value)
      case CHECKCAST if value.isInstanceOf[ParamValue] =>
        new ParamValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc))
      case INSTANCEOF if value.isInstanceOf[ParamValue] =>
        InstanceOfCheckValue()
      case NEWARRAY | ANEWARRAY if propagate_? =>
        NotNullValue(super.unaryOperation(insn, value).getType)
      case _ =>
        super.unaryOperation(insn, value)
    }
  }

  override def binaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue): BasicValue = {
    insn.getOpcode match {
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD | PUTFIELD
        if nullAnalysis && v1.isInstanceOf[ParamValue] =>
          dereferenced = true
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  override def ternaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue, v3: BasicValue): BasicValue = {
    insn.getOpcode match {
      case IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE
        if nullAnalysis && v1.isInstanceOf[ParamValue] =>
        dereferenced = true
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  @switch
  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val propagate_? = isResultOrigin(insn)
    val opCode = insn.getOpcode
    val shift = if (opCode == INVOKESTATIC) 0 else 1
    if ((opCode == INVOKESPECIAL || opCode == INVOKEINTERFACE || opCode == INVOKEVIRTUAL) && nullAnalysis && values.get(0).isInstanceOf[ParamValue]) {
      dereferenced = true
      return super.naryOperation(insn, values)
    }
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL | INVOKEINTERFACE  if propagate_? =>
        val stable = opCode == INVOKESTATIC || opCode == INVOKESPECIAL
        val mNode = insn.asInstanceOf[MethodInsnNode]
        val method = Method(mNode.owner, mNode.name, mNode.desc)
        val retType = Type.getReturnType(mNode.desc)
        val isRefRetType = retType.getSort == Type.OBJECT || retType.getSort == Type.ARRAY
        val isBooleanRetType = retType == Type.BOOLEAN_TYPE
        if (isRefRetType || isBooleanRetType)
          direction match {
            case InOut(_, inValue) =>
              var keys = Set[Key]()
              for (i <- shift until values.size()) {
                if (values.get(i).isInstanceOf[ParamValue])
                  keys = keys + Key(method, InOut(i - shift, inValue), stable)
              }
              if (isRefRetType)
                keys = keys + Key(method, Out, stable)
              if (keys.nonEmpty)
                return CallResultValue(retType, keys)
            case _ =>
              if (isRefRetType)
                return CallResultValue(retType, Set(Key(method, Out, stable)))
          }
        super.naryOperation(insn, values)
      case MULTIANEWARRAY if propagate_? =>
        NotNullValue(super.naryOperation(insn, values).getType)
      case _ =>
        super.naryOperation(insn, values)
    }
  }
}
