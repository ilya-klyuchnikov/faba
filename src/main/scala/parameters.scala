package faba.parameters

import org.objectweb.asm.Type
import org.objectweb.asm.tree.analysis.{BasicInterpreter, Frame, BasicValue}
import org.objectweb.asm.tree.{MethodInsnNode, TypeInsnNode, JumpInsnNode, AbstractInsnNode}
import org.objectweb.asm.Opcodes._

import faba.analysis.{Utils => AnalysisUtils, _}
import faba.cfg._
import faba.data._
import faba.engine._

object `package` {

  type SoP = Set[Set[Key]]

  implicit class SopOps(val sop1: SoP) {
    def join(sop2: SoP): SoP =
      sop1 ++ sop2

    def meet(sop2: SoP): SoP =
      for {
        prod1 <- sop1
        prod2 <- sop2
      } yield prod1 ++ prod2
  }

}

sealed trait Result
case object Identity extends Result
case object Error extends Result
case object Return extends Result
case object NPE extends Result
case class ConditionalNPE(sop: SoP) extends Result {
  if (sop.map(_.size).sum > 30) throw new LimitReachedException
}

object ConditionalNPE {
  def apply(passing: Key): ConditionalNPE = ConditionalNPE(Set(Set(passing)))
}

object Result {

  def join(r1: Result, r2: Result): Result = (r1, r2) match {
    case (Error, _) => r2
    case (_, Error) => r1
    case (Identity, _) => r2
    case (_, Identity) => r1
    case (Return, _) => Return
    case (_, Return) => Return
    case (NPE, NPE) => NPE
    case (NPE, r2: ConditionalNPE) => r2
    case (r1: ConditionalNPE, NPE) => r1
    case (ConditionalNPE(e1), ConditionalNPE(e2)) => ConditionalNPE(e1 join e2)
  }

  def combineNullable(r1: Result, r2: Result): Result = (r1, r2) match {
    case (Error, _) => r2
    case (_, Error) => r1
    case (Identity, _) => r2
    case (_, Identity) => r1
    case (Return, _) => r2
    case (_, Return) => r1
    case (NPE, _) => NPE
    case (_, NPE) => NPE
    case (ConditionalNPE(e1), ConditionalNPE(e2)) => ConditionalNPE(e1 join e2)
  }

  def meet(r1: Result, r2: Result): Result = (r1, r2) match {
    case (Identity, _) => r2
    case (Return, _) => r2
    case (_, Return) => r1
    case (NPE, _) => NPE
    case (_, NPE) => NPE
    case (Error, _) => Error
    case (_, Error) => Error
    // Oops - cycle dominates
    case (_, Identity) => Identity
    case (ConditionalNPE(e1), ConditionalNPE(e2)) => ConditionalNPE(e1 meet e2)
  }

  def subMeet(r1: Result, r2: Result): Result = (r1, r2) match {
    case (Identity, _) => r2
    case (_, Identity) => r1
    case (Return, _) => r2
    case (_, Return) => r1
    case (NPE, _) => NPE
    case (_, NPE) => NPE
    case (Error, _) => Error
    case (_, Error) => Error
    case (ConditionalNPE(e1), ConditionalNPE(e2)) => ConditionalNPE(e1 meet e2)
  }
}

object NotNullInConstraint {
  // (taken: Boolean, hasCompanions: Boolean)
  val TAKEN = 1 // 1 << 0
  val HAS_COMPANIONS = 2 //1 << 1

  // (x != null) / (x instanceOf ..) was proceeded
  def isTaken(constraint: Int) = (constraint & TAKEN) != 0

  // some previous configuration is foo(param) -
  // hasCompanions = true means that it is possible indirect dereference
  def hasCompanions(constraint: Int) = (constraint & HAS_COMPANIONS) != 0
}

object NotNullInAnalysis {
  // For inference of @NotNull parameters we need to combine information from all configurations,
  // not just from leaf configurations.
  // So we need to build and traverse graph of configurations in some tricky order.
  // For this purpose we maintain "pending list" of what to do.

  /**
   * Element of pending list - pending action.
   */
  sealed trait PendingAction

  /**
   * "Forward step". Driving of current configuration.
   * @param state state to process
   *
   * @see faba.parameters.NotNullInAnalysis#processState(faba.analysis.State)
   */
  case class ProceedState(state: State) extends PendingAction

  /**
   * "Combine step". Calculates "approximation" (see the paper) of behavior from some configuration.
   * Given local delta and sub-sigmas, computes current sigma.
   *
   * A note about states:
   * there is a micro optimization: driving of straight section/piece of graph of configurations without push/pop of actions.
   * States are states/configurations from this straight section of a graph.
   *
   * @param states a list of states representing the straight section of a graph.
   * @param subResult - local delta (see the paper), produced by driving of straight section.
   * @param indices - indices of child states
   */
  case class MakeResult(states: List[State], subResult: Result, indices: List[Int]) extends PendingAction

  /**
   * Reusable pending list (pending stack) for push/pop actions during analyses.
   * @see faba.parameters.NotNullInAnalysis#pending
   */
  val sharedPendingStack = new Array[PendingAction](LimitReachedException.limit)

  /**
   * Reusable storage of sub results during analyses.
   * @see faba.parameters.NotNullInAnalysis#results
   */
  val sharedResults = new Array[Result](LimitReachedException.limit)
}

class NotNullInAnalysis(val richControlFlow: RichControlFlow, val direction: Direction, val stable: Boolean) extends Analysis[Result] {
  import NotNullInAnalysis._

  val results = NotNullInAnalysis.sharedResults
  val pending = NotNullInAnalysis.sharedPendingStack

  /**
   *
   * @param delta
   * @param subResults
   * @return
   */
  def combineResults(delta: Result, subResults: List[Result]): Result =
    Result.meet(delta, subResults.reduce(Result.join))

  override def mkEquation(result: Result): Equation[Key, Value] = result match {
    case Identity | Return | Error =>
      Equation(aKey, Final(Values.Top))
    case NPE =>
      Equation(aKey, Final(Values.NotNull))
    case ConditionalNPE(cnf) =>
      Equation(aKey, Pending(cnf.map(p => Component(Values.Top, p))))
  }

  var npe = false

  private var pendingTop: Int = 0

  final def pendingPush(action: PendingAction) {
    pending(pendingTop) = action
    pendingTop += 1
  }

  final def pendingPop(): PendingAction = {
    pendingTop -= 1
    pending(pendingTop)
  }

  def analyze(): Equation[Key, Value] = {
    pendingPush(ProceedState(createStartState()))

    while (pendingTop > 0 && earlyResult.isEmpty) pendingPop() match {
      case MakeResult(states, delta, subIndices) =>
        val result = combineResults(delta, subIndices.map(results))
        for (state <- states) {
          val insnIndex = state.conf.insnIndex
          results(state.index) = result
          computed(insnIndex) = state :: computed(insnIndex)
        }
      case ProceedState(state) =>
        processState(state)
    }

    mkEquation(earlyResult.getOrElse(results(0)))
  }

  override def processState(fState: State): Unit = {

    var state = fState
    var states: List[State] = Nil
    var subResult: Result = Identity

    while (true) {
      computed(state.conf.insnIndex).find(prevState => AnalysisUtils.stateEquiv(state, prevState)) match {
        case Some(ps) =>
          results(state.index) = results(ps.index)
          if (states.nonEmpty)
            pendingPush(MakeResult(states, subResult, List(ps.index)))
          return
        case None =>
      }


      val stateIndex = state.index
      val conf = state.conf
      val insnIndex = conf.insnIndex
      val history = state.history

      val fold = dfsTree.loopEnters(insnIndex) && history.exists(prevConf => AnalysisUtils.isInstance(conf, prevConf))

      if (fold) {
        results(stateIndex) = Identity
        computed(insnIndex) = state :: computed(insnIndex)
        if (states.nonEmpty)
          pendingPush(MakeResult(states, subResult, List(stateIndex)))
        return
      }

      val frame = conf.frame
      val insnNode = methodNode.instructions.get(insnIndex)
      val nextHistory = if (dfsTree.loopEnters(insnIndex)) conf :: history else history
      val (nextFrame, localSubResult) = execute(frame, insnNode)
      val notEmptySubResult = localSubResult != Identity

      // local "summing"
      val subResult2 = Result.subMeet(subResult, localSubResult)
      val noSwitch = subResult == subResult2
      subResult = subResult2

      if (localSubResult == NPE) {
        // npe was detected, storing this fact for further analyses
        npe = true
        results(stateIndex) = NPE
        computed(insnIndex) = state :: computed(insnIndex)
        pendingPush(MakeResult(states, subResult, List(stateIndex)))
        return
      }

      val constraint = state.constraint
      // the constant will be inlined by javac
      val companionsNow = if (localSubResult != Identity) 2 else 0
      val constraint1 = constraint | companionsNow

      insnNode.getOpcode match {
        case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
          if (!NotNullInConstraint.hasCompanions(constraint)) {
            earlyResult = Some(Return)
            return
          } else {
            results(stateIndex) = Return
            computed(insnIndex) = state :: computed(insnIndex)
            // important to put subResult
            if (states.nonEmpty)
              pendingPush(MakeResult(states, subResult, List(stateIndex)))
            return
          }
        case ATHROW if NotNullInConstraint.isTaken(constraint) =>
          results(stateIndex) = NPE
          npe = true
          computed(insnIndex) = state :: computed(insnIndex)
          if (states.nonEmpty)
            pendingPush(MakeResult(states, subResult, List(stateIndex)))
          return
        case ATHROW =>
          results(stateIndex) = Error
          computed(insnIndex) = state :: computed(insnIndex)
          if (states.nonEmpty)
            pendingPush(MakeResult(states, subResult, List(stateIndex)))
          return
        case IFNONNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = insnIndex + 1
          val nextState = State(genId(), Conf(nextInsnIndex, nextFrame), nextHistory, constraint1 | 1)
          states = state :: states
          state = nextState
        case IFNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nextState = State(genId(), Conf(nextInsnIndex, nextFrame), nextHistory, constraint1 | 1)
          states = state :: states
          state = nextState
        case IFEQ if popValue(frame).isInstanceOf[ParamInstanceOfCheckValue] =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nextState = State(genId(), Conf(nextInsnIndex, nextFrame), nextHistory, constraint1 | 1)
          states = state :: states
          state = nextState
        case IFNE if popValue(frame).isInstanceOf[ParamInstanceOfCheckValue] =>
          val nextInsnIndex = insnIndex + 1
          val nextState = State(genId(), Conf(nextInsnIndex, nextFrame), nextHistory, constraint1 | 1)
          states = state :: states
          state = nextState
        case _ =>
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
              State(genId(), Conf(nextInsnIndex, nextFrame1), nextHistory, constraint1)
          }
          states = state :: states
          if (nextStates.size == 1 && noSwitch) {
            state = nextStates.head
          } else {
            pendingPush(MakeResult(states, subResult, nextStates.map(_.index)))
            nextStates.foreach {s => pendingPush(ProceedState(s))}
            return
          }
      }
    }
  }

  private def execute(frame: Frame[BasicValue], insnNode: AbstractInsnNode) = insnNode.getType match {
    case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
      (frame, Identity)
    case _ =>
      val nextFrame = new Frame(frame)
      NonNullInterpreter.reset()
      nextFrame.execute(insnNode, NonNullInterpreter)
      (nextFrame, NonNullInterpreter.getSubResult)
  }
}

case class NullableInConstraint(taken: Boolean)

object NullableInConstraint {
  val TAKEN = 1
  val NOT_TAKEN = 0
}

object NullableInAnalysis {
  val sharedPendingStack = new Array[State](LimitReachedException.limit)
}

class NullableInAnalysis(val richControlFlow: RichControlFlow, val direction: Direction, val stable: Boolean) extends Analysis[Result] {

  val pending = NullableInAnalysis.sharedPendingStack

  override def mkEquation(result: Result): Equation[Key, Value] = result match {
    case NPE => Equation(aKey, Final(Values.Top))
    case Identity | Return | Error => Equation(aKey, Final(Values.Null))
    case ConditionalNPE(cnf) =>
      Equation(aKey, Pending(cnf.map(p => Component(Values.Top, p))))
  }

  private var myResult: Result = Identity

  private var pendingTop: Int = 0

  final def pendingPush(state: State) {
    pending(pendingTop) = state
    pendingTop += 1
  }

  final def pendingPop(): State = {
    pendingTop -= 1
    pending(pendingTop)
  }

  def analyze(): Equation[Key, Value] = {
    pendingPush(createStartState())

    while (pendingTop > 0 && earlyResult.isEmpty)
      processState(pendingPop())

    mkEquation(earlyResult.getOrElse(myResult))
  }

  override def processState(fState: State): Unit = {

    var state = fState

    while (true) {
      computed(state.conf.insnIndex).find(prevState => AnalysisUtils.stateEquiv(state, prevState)) match {
        case Some(ps) =>
          return
        case None =>
      }

      val conf = state.conf
      val insnIndex = conf.insnIndex
      val history = state.history

      val isLoopEnter = dfsTree.loopEnters(insnIndex)
      val fold = isLoopEnter && history.exists(prevConf => AnalysisUtils.isInstance(conf, prevConf))

      computed(insnIndex) = state :: computed(insnIndex)

      if (fold)
        return

      val taken = state.constraint
      val frame = conf.frame
      val insnNode = methodNode.instructions.get(insnIndex)
      val nextHistory = if (isLoopEnter) conf :: history else history
      val (nextFrame, localSubResult) = execute(frame, insnNode)

      if (localSubResult == NPE) {
        earlyResult = Some(NPE)
        return
      }

      if (localSubResult.isInstanceOf[ConditionalNPE])
        myResult = Result.combineNullable(myResult, localSubResult)

      insnNode.getOpcode match {
        case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
          if (insnNode.getOpcode == ARETURN && popValue(frame).isInstanceOf[ParamValue]) {
            earlyResult = Some(NPE)
            return
          }
          return
        case ATHROW if state.constraint == 1 =>
          earlyResult = Some(NPE)
          return
        case ATHROW =>
          return
        case IFNONNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = insnIndex + 1
          state = State(genId(), Conf(nextInsnIndex, nextFrame), nextHistory, 1)
        case IFNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          state = State(genId(), Conf(nextInsnIndex, nextFrame), nextHistory, 1)
        case IFEQ if popValue(frame).isInstanceOf[ParamInstanceOfCheckValue] =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          state = State(genId(), Conf(nextInsnIndex, nextFrame), nextHistory, 1)
        case IFNE if popValue(frame).isInstanceOf[ParamInstanceOfCheckValue] =>
          val nextInsnIndex = insnIndex + 1
          state = State(genId(), Conf(nextInsnIndex, nextFrame), nextHistory, 1)
        case _ =>
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
              State(genId(), Conf(nextInsnIndex, nextFrame1), nextHistory, taken)
          }
          if (nextStates.size == 1) {
            state = nextStates.head
          } else {
            nextStates.foreach {s => pendingPush(s)}
            return
          }
      }
    }
  }

  private def execute(frame: Frame[BasicValue], insnNode: AbstractInsnNode) = insnNode.getType match {
    case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
      (frame, Identity)
    case _ =>
      val nextFrame = new Frame(frame)
      NullableInterpreter.reset()
      nextFrame.execute(insnNode, NullableInterpreter)
      (nextFrame, NullableInterpreter.getSubResult)
  }
}

abstract class Interpreter extends BasicInterpreter {
  val nullable: Boolean
  protected var _subResult: Result = Identity
  final def reset(): Unit = {
    _subResult = Identity
  }

  def combine(res1: Result, res2: Result): Result

  def getSubResult: Result =
    _subResult

  final override def unaryOperation(insn: AbstractInsnNode, value: BasicValue): BasicValue = {
    insn.getOpcode match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER if value.isInstanceOf[ParamValue] =>
        _subResult = NPE
      case CHECKCAST if value.isInstanceOf[ParamValue] =>
        return new ParamValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc))
      case INSTANCEOF if value.isInstanceOf[ParamValue] =>
        return ParamInstanceOfCheckValue()
      case _ =>
    }
    super.unaryOperation(insn, value)
  }

  final override def binaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue): BasicValue = {
    insn.getOpcode match {
      case PUTFIELD
        if v1.isInstanceOf[ParamValue] || (nullable && v2.isInstanceOf[ParamValue]) =>
        _subResult = NPE
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD if v1.isInstanceOf[ParamValue] =>
        _subResult = NPE
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  final override def ternaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue, v3: BasicValue): BasicValue = {
    insn.getOpcode match {
      case IASTORE | LASTORE | FASTORE | DASTORE | BASTORE | CASTORE | SASTORE
        if v1.isInstanceOf[ParamValue] =>
        _subResult = NPE
      case AASTORE
        if v1.isInstanceOf[ParamValue] || (nullable && v3.isInstanceOf[ParamValue]) =>
        _subResult = NPE
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  final override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    val static = opCode == INVOKESTATIC
    val shift = if (static) 0 else 1
    if ((opCode == INVOKESPECIAL || opCode == INVOKEINTERFACE || opCode == INVOKEVIRTUAL) && values.get(0).isInstanceOf[ParamValue]) {
      _subResult = NPE
    }
    if (nullable && opCode == INVOKEINTERFACE) {
      for (i <- shift until values.size()) {
        if (values.get(i).isInstanceOf[ParamValue]) {
          _subResult = NPE
          return super.naryOperation(insn, values)
        }
      }
      return super.naryOperation(insn, values)
    }
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL =>
        val stable = opCode == INVOKESTATIC || opCode == INVOKESPECIAL
        val mNode = insn.asInstanceOf[MethodInsnNode]
        for (i <- shift until values.size()) {
          if (values.get(i).isInstanceOf[ParamValue]) {
            val method = Method(mNode.owner, mNode.name, mNode.desc)
            _subResult = combine(_subResult, ConditionalNPE(Key(method, In(i - shift), stable)))
          }
        }
      case _ =>
    }
    super.naryOperation(insn, values)
  }
}

object NonNullInterpreter extends Interpreter {
  override val nullable = false
  override def combine(res1: Result, res2: Result): Result = Result.meet(res1, res2)

}

object NullableInterpreter extends Interpreter {
  override val nullable = true
  override def combine(res1: Result, res2: Result): Result = Result.join(res1, res2)
}
