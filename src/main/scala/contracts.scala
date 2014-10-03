package faba.contracts

import faba.asm.Origins

import scala.annotation.switch

import org.objectweb.asm.{Opcodes, Handle, Type}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.analysis.{BasicValue, BasicInterpreter, Frame}
import org.objectweb.asm.tree._

import faba.analysis.{Utils => AnalysisUtils, _}
import faba.cfg._
import faba.data._
import faba.engine._

object InOutAnalysis {
  // Shared (between analysis runs) array/stack of pending states.
  // Since:
  //  1. We know upper bound of its size (LimitReachedException.limit)
  //  2. There is not need to empty this array on each run (it is used as stack)
  val sharedPendingStack = new Array[State](LimitReachedException.limit)
}

class InOutAnalysis(val richControlFlow: RichControlFlow,
                    val direction: Direction,
                    resultOrigins: Origins,
                    val stable: Boolean,
                    val _noCycle: Boolean) extends Analysis[Result[Key, Value]] {

  type MyResult = Result[Key, Value]
  implicit val contractsLattice = ELattice(Values.Bot, Values.Top)
  val propagate = true

  val pendingStack = InOutAnalysis.sharedPendingStack
  // there is no need to generalize `this` (local var 0) for instance methods
  val generalizeShift = if ((methodNode.access & ACC_STATIC) == 0) 1 else 0
  val nullAnalysis = direction match {
    case InOut(_, Values.Null) => true
    case _ => false
  }

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

  def checkEarlyResult(): Unit = myResult match {
    case Final(Values.Top) =>
      earlyResult = Some(myResult)
    case _ =>
  }

  private var myResult: MyResult = identity

  private var pendingStackTop: Int = 0

  final def pendingPush(st: State) {
    pendingStack(pendingStackTop) = st
    pendingStackTop += 1
  }

  final def pendingPop(): State = {
    pendingStackTop -= 1
    pendingStack(pendingStackTop)
  }

  def analyze(): Equation[Key, Value] = {
    // give up if we cannot encode constraints via integers
    if (resultOrigins.size > 32)
      return Equation(aKey, Final(Values.Top))

    pendingPush(createStartState())

    while (pendingStackTop > 0 && earlyResult.isEmpty)
      processState(pendingPop())

    mkEquation(earlyResult.getOrElse(myResult))
  }

  override def processState(fState: State): Unit = {

    var state = fState
    var states: List[State] = Nil

    while (true) {
      // sharing
      computed(state.conf.insnIndex).find(prevState => AnalysisUtils.stateEquiv(state, prevState)) match {
        case Some(ps) =>
          // was computed before
          return
        case None =>
      }

      val preConf = state.conf
      val insnIndex = preConf.insnIndex
      val loopEnter = dfsTree.loopEnters(insnIndex)
      val history = state.history

      // todo - is it ok not look into taken/not-taken
      // possible improvement - more restrictions
      val fold = loopEnter && history.exists(prevConf => confInstance(preConf, prevConf))

      if (fold) {
        computed(insnIndex) = state :: computed(insnIndex)
        return
      }

      val conf = if (loopEnter && !propagate) generalize(preConf) else preConf

      val frame = conf.frame
      val insnNode = methodNode.instructions.get(insnIndex)
      val nextHistory = if (loopEnter) conf :: history else history
      val nextFrame = execute(frame, insnNode)

      val dereferencedHere: Int = interpreter.dereferenced


      val dereferenced = state.constraint | dereferencedHere

      // executed only during null
      if (nullAnalysis && interpreter.dereferencedParam) {
        computed(insnIndex) = state :: computed(insnIndex)
        // enough to break this branch - it will be bottom, will not contribute to the result
        return
      }

      insnNode.getOpcode match {
        case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
          popValue(frame) match {
            case FalseValue() =>
              myResult = myResult join Final(Values.False)
            case TrueValue() =>
              myResult = myResult join Final(Values.True)
            case NotNullValue(_) =>
              myResult = myResult join Final(Values.NotNull)
            case ParamValue(_) =>
              val InOut(_, in) = direction
              myResult = myResult join Final(in)
            case tr: Trackable if (dereferenced & resultOrigins.instructionsMap(tr.origin)) != 0 =>
              myResult = myResult join Final(Values.NotNull)
            case NThParamValue(n, _) if (dereferenced & resultOrigins.parametersMap(n)) != 0 =>
              myResult = myResult join Final(Values.NotNull)
            case NullValue(_) =>
              myResult = myResult join Final(Values.Null)
            case CallResultValue(_, _, keys) =>
              myResult = myResult join Pending[Key, Value](Set(Component(Values.Top, keys)))
            case _ =>
              earlyResult = Some(Final(Values.Top))
              return
          }
          computed(insnIndex) = state :: computed(insnIndex)
          checkEarlyResult()
          return
        case ATHROW =>
          computed(insnIndex) = state :: computed(insnIndex)
          return
        case IFNONNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = (direction: @unchecked) match {
            case InOut(_, Values.Null) =>
              insnIndex + 1
            case InOut(_, Values.NotNull) =>
              methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          }
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, dereferenced)
          states = state :: states
          state = nextState
        case IFNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = (direction: @unchecked) match {
            case InOut(_, Values.Null) =>
              methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
            case InOut(_, Values.NotNull) =>
              insnIndex + 1
          }
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, dereferenced)
          states = state :: states
          state = nextState

        case IFNONNULL if propagate && popValue(frame).isInstanceOf[NThParamValue] =>
          val nullInsn = insnIndex + 1
          val notNullInsn = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val n = popValue(frame).asInstanceOf[NThParamValue].n
          val nullState = State(mkId(), Conf(nullInsn, nextFrame), nextHistory, dereferenced)
          val notNullState = State(mkId(), Conf(notNullInsn, nextFrame), nextHistory, dereferenced | resultOrigins.parametersMap(n))
          pendingPush(nullState)
          pendingPush(notNullState)
          return
        case IFNONNULL if propagate && popValue(frame).isInstanceOf[Trackable] =>
          val nullInsn = insnIndex + 1
          val notNullInsn = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val orig = popValue(frame).asInstanceOf[Trackable].origin
          val nullState = State(mkId(), Conf(nullInsn, nextFrame), nextHistory, dereferenced)
          val notNullState = State(mkId(), Conf(notNullInsn, nextFrame), nextHistory, dereferenced | resultOrigins.instructionsMap(orig))
          pendingPush(nullState)
          pendingPush(notNullState)
          return
        case IFNULL if propagate && popValue(frame).isInstanceOf[NThParamValue] =>
          val nullInsn = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val notNullInsn = insnIndex + 1
          val n = popValue(frame).asInstanceOf[NThParamValue].n
          val nullState = State(mkId(), Conf(nullInsn, nextFrame), nextHistory, dereferenced)
          val notNullState = State(mkId(), Conf(notNullInsn, nextFrame), nextHistory, dereferenced | resultOrigins.parametersMap(n))
          pendingPush(nullState)
          pendingPush(notNullState)
          return
        case IFNULL if propagate && popValue(frame).isInstanceOf[Trackable] =>
          val nullInsn = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val notNullInsn = insnIndex + 1
          val orig = popValue(frame).asInstanceOf[Trackable].origin
          val nullState = State(mkId(), Conf(nullInsn, nextFrame), nextHistory, dereferenced)
          val notNullState = State(mkId(), Conf(notNullInsn, nextFrame), nextHistory, dereferenced | resultOrigins.instructionsMap(orig))
          pendingPush(nullState)
          pendingPush(notNullState)
          return

        case IFEQ if popValue(frame).isInstanceOf[InstanceOfCheckValue] && optIn == Some(Values.Null) =>
          val nextInsnIndex =
            methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, dereferenced)
          states = state :: states
          state = nextState
        case IFNE if popValue(frame).isInstanceOf[InstanceOfCheckValue] && optIn == Some(Values.Null) =>
          val nextInsnIndex = insnIndex + 1
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, dereferenced)
          state = nextState

        case _ =>
          // we touch this!
          computed(insnIndex) = state :: computed(insnIndex)
          val nextInsnIndices = controlFlow.transitions(insnIndex)
          val nextStates = nextInsnIndices.map {
            nextInsnIndex =>
              val nextFrame1 = if (controlFlow.errors(nextInsnIndex) && controlFlow.errorTransitions(insnIndex -> nextInsnIndex)) {
                val handler = new Frame(frame)
                handler.clearStack()
                handler.push(new BasicValue(Type.getType("java/lang/Throwable")))
                handler
              } else {
                nextFrame
              }
              State(mkId(), Conf(nextInsnIndex, nextFrame1), nextHistory, dereferenced)
          }
          states = state :: states
          if (nextStates.size == 1) {
            state = nextStates.head
          } else {
            nextStates.foreach(pendingPush)
            return
          }
      }
    }
  }

  private def execute(frame: Frame[BasicValue], insnNode: AbstractInsnNode) = insnNode.getType match {
    case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
      interpreter.reset()
      frame
    case _ =>
      interpreter.reset()
      val nextFrame = new Frame(frame)
      nextFrame.execute(insnNode, interpreter)
      nextFrame
  }

  // in-place generalization
  def generalize(conf: Conf): Conf = {
    val frame = new Frame(conf.frame)
    for (i <- generalizeShift until frame.getLocals) frame.getLocal(i) match {
      case CallResultValue(_, tp, _) =>
        frame.setLocal(i, new BasicValue(tp))
      case TrueValue() =>
        frame.setLocal(i, BasicValue.INT_VALUE)
      case FalseValue() =>
        frame.setLocal(i, BasicValue.INT_VALUE)
      case NullValue(_) =>
        frame.setLocal(i, BasicValue.UNINITIALIZED_VALUE)
      case NotNullValue(tp) =>
        frame.setLocal(i, new BasicValue(tp))
      case _ =>
    }

    val stack = (0 until frame.getStackSize).map(frame.getStack)
    frame.clearStack()

    for (v <- stack) v match {
      case CallResultValue(_, tp, _) =>
        frame.push(new BasicValue(tp))
      case TrueValue() =>
        frame.push(BasicValue.INT_VALUE)
      case FalseValue() =>
        frame.push(BasicValue.INT_VALUE)
      case NullValue(_) =>
        frame.push(BasicValue.UNINITIALIZED_VALUE)
      case NotNullValue(tp) =>
        frame.push(new BasicValue(tp))
      case _ =>
        frame.push(v)
    }
    Conf(conf.insnIndex, frame)
  }

  // customization: if param is a possible result, it is trackable
  override def createStartFrame(): Frame[BasicValue] = {
    val frame = new Frame[BasicValue](methodNode.maxLocals, methodNode.maxStack)
    val returnType = Type.getReturnType(methodNode.desc)
    val returnValue = if (returnType == Type.VOID_TYPE) null else new BasicValue(returnType)
    frame.setReturn(returnValue)

    val args = Type.getArgumentTypes(methodNode.desc)
    var local = 0
    if ((methodNode.access & Opcodes.ACC_STATIC) == 0) {
      val basicValue = new NotNullValue(Type.getObjectType(controlFlow.className))
      frame.setLocal(local, basicValue)
      local += 1
    }
    for (i <- 0 until args.size) {
      val value = direction match {
        case InOut(`i`, _) =>
          new ParamValue(args(i))
        case In(`i`) =>
          new ParamValue(args(i))
        case _ =>
          if (resultOrigins.parameters(i))
            NThParamValue(i, args(i))
          else
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
}

case class InOutInterpreter(direction: Direction, insns: InsnList, resultOrigins: Origins) extends BasicInterpreter {
  val insnOrigins = resultOrigins.instructions

  def index(insn: AbstractInsnNode) =
    insns.indexOf(insn)

  // whether a null-param was dereferenced execution
  // this flag is set ONLY for `null->?` analysis
  var dereferencedParam = false
  var dereferenced: Int = 0

  def reset(): Unit = {
    dereferencedParam = false
    dereferenced = 0
  }

  val nullAnalysis = direction match {
    case InOut(_, Values.Null) => true
    case _ => false
  }

  @switch
  override def newOperation(insn: AbstractInsnNode): BasicValue = {
    val propagate_? = insnOrigins(insns.indexOf(insn))
    insn.getOpcode match {
      case ICONST_0 if propagate_? =>
        FalseValue()
      case ICONST_1 if propagate_? =>
        TrueValue()
      case ACONST_NULL if propagate_? =>
        NullValue(index(insn))
      case GETSTATIC if propagate_? =>
        TrackableBasicValue(index(insn), super.newOperation(insn).getType)
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
    val propagate_? = insnOrigins(insns.indexOf(insn))
    insn.getOpcode match {
      case GETFIELD =>
        value match {
          case ParamValue(_) =>
            dereferencedParam = true
          case NThParamValue(n, _) =>
            dereferenced = resultOrigins.parametersMap(n)
          case tr: Trackable =>
            dereferenced = resultOrigins.instructionsMap(tr.origin)
          case _ =>
        }
        if (propagate_?)
          TrackableBasicValue(index(insn), super.unaryOperation(insn, value).getType)
        else
          super.unaryOperation(insn, value)
      case ARRAYLENGTH | MONITORENTER =>
        value match {
          case ParamValue(_) =>
            dereferencedParam = true
          case NThParamValue(n, _) =>
            dereferenced = resultOrigins.parametersMap(n)
          case tr: Trackable =>
            dereferenced = resultOrigins.instructionsMap(tr.origin)
          case _ =>
        }
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
    val propagate_? = insnOrigins(insns.indexOf(insn))
    insn.getOpcode match {
      case AALOAD =>
        v1 match {
          case ParamValue(_) =>
            dereferencedParam = true
          case NThParamValue(n, _) =>
            dereferenced = resultOrigins.parametersMap(n)
          case tr: Trackable =>
            dereferenced = resultOrigins.instructionsMap(tr.origin)
          case _ =>
        }
        if (propagate_?)
          TrackableBasicValue(index(insn), super.binaryOperation(insn, v1, v2).getType)
        else
          super.binaryOperation(insn, v1, v2)
      case IALOAD | LALOAD | FALOAD | DALOAD | BALOAD | CALOAD | SALOAD | PUTFIELD =>
        v1 match {
          case ParamValue(_) =>
            dereferencedParam = true
          case NThParamValue(n, _) =>
            dereferenced = resultOrigins.parametersMap(n)
          case tr: Trackable =>
            dereferenced = resultOrigins.instructionsMap(tr.origin)
          case _ =>
        }
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  override def ternaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue, v3: BasicValue): BasicValue = {
    insn.getOpcode match {
      case IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE =>
        v1 match {
          case ParamValue(_) =>
            dereferencedParam = true
          case NThParamValue(n, _) =>
            dereferenced = resultOrigins.parametersMap(n)
          case tr: Trackable =>
            dereferenced = resultOrigins.instructionsMap(tr.origin)
          case _ =>
        }
      case _ =>
    }
    null
  }

  @switch
  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val propagate_? = insnOrigins(insns.indexOf(insn))
    val opCode = insn.getOpcode
    val shift = if (opCode == INVOKESTATIC) 0 else 1
    if (opCode == INVOKESPECIAL || opCode == INVOKEINTERFACE || opCode == INVOKEVIRTUAL) {
      values.get(0) match {
        case ParamValue(_) =>
          dereferencedParam = true
          if (nullAnalysis)
            return super.naryOperation(insn, values)
        case NThParamValue(n, _) =>
          dereferenced = resultOrigins.parametersMap(n)
        case tr: Trackable =>
          dereferenced = resultOrigins.instructionsMap(tr.origin)
        case _ =>
      }
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
          // TODO - hack into parameters here
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
                return CallResultValue(index(insn), retType, keys)
            case _ =>
              if (isRefRetType)
                return CallResultValue(index(insn), retType, Set(Key(method, Out, stable)))
          }
        super.naryOperation(insn, values)
      case MULTIANEWARRAY if propagate_? =>
        NotNullValue(super.naryOperation(insn, values).getType)
      case _ =>
        super.naryOperation(insn, values)
    }
  }
}
