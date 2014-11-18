package faba.analysis.parameters

import faba.analysis._
import faba.data._
import faba.engine._

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.Type
import org.objectweb.asm.tree.analysis.{BasicInterpreter, BasicValue, Frame}
import org.objectweb.asm.tree._

/**
 * Approximation of a method execution (subgraph of a graph of configurations)
 * for @NotNull parameter analysis.
 */
sealed trait ExecutionResult {
  def toResult: Result[Key, Value]
}

/**
 * Approximation of a number of steps of a method execution
 * (subpath of a graph of configurations, this subpath does NOT include leaves)
 * for @NotNull parameter analysis.
 */
sealed trait StepsResult

/**
 * Cycle in the program (fold in a graph of configurations).
 */
case object Cycle extends ExecutionResult {
  override def toResult: Result[Key, Value] =
    Final(Values.Top)
}

/**
 * An error (not caused by null value of the parameter)
 */
case object Error extends ExecutionResult {
  override def toResult: Result[Key, Value] =
    Final(Values.Top)
}

/**
 *  Execution reaches RETURN instruction without any chance to produce NPE.
 */
case object Return extends ExecutionResult {
  override def toResult: Result[Key, Value] =
    Final(Values.Top)
}

/**
 * This approximation is NPE if formula results in @NotNull.
 *
 * @param sop SumOfProduct formula of dependencies.
 */
case class ConditionalNPE(sop: ExecutionResult.SoP) extends ExecutionResult with StepsResult {
  if (sop.map(_.size).sum > 30) throw new LimitReachedException

  override def toResult: Result[Key, Value] =
    Pending(sop.map(p => Product(Values.Top, p)))
}

/**
 * Error caused by null-value of the parameter.
 * Dereferencing error or an assertion.
 */
case object NPE extends ExecutionResult with StepsResult {
  override def toResult: Result[Key, Value] =
    Final(Values.NotNull)
}

/**
 * Steps without any chance to produce NPE.
 */
case object Identity extends StepsResult

object ConditionalNPE {
  def apply(passing: Key): ConditionalNPE = ConditionalNPE(Set(Set(passing)))
}

object ExecutionResult {

  // pure version of sum of products
  type SoP = Set[Set[Key]]

  object SoP {
    def join(sop1: SoP, sop2: SoP) =
      sop1 ++ sop2

    def meet(sop1: SoP, sop2: SoP) =
      for {
        prod1 <- sop1
        prod2 <- sop2
      } yield prod1 ++ prod2
  }

  /**
   * Joins approximations of two paths of executions (for `@NotNull` parameter inference)
   *
   *     joined
   *       / \
   *      r1 r2
   *
   * `r1` and `r2` correspond to "complete" "sub-graphs"
   *
   * @param r1 approximation on the left path of execution
   * @param r2 approximation on the right path of execution
   * @return sound joined approximation
   */
  def join(r1: ExecutionResult, r2: ExecutionResult): ExecutionResult = (r1, r2) match {
    case (Error|Cycle, _) => r2
    case (_, Error|Cycle) => r1
    case (Return, _) => Return
    case (_, Return) => Return
    case (NPE, NPE) => NPE
    case (NPE, r2: ConditionalNPE) => r2
    case (r1: ConditionalNPE, NPE) => r1
    case (ConditionalNPE(e1), ConditionalNPE(e2)) => ConditionalNPE(SoP.join(e1, e2))
  }

  /**
   *
   * Combines approximation of a subpath and approximation of a complete subgraph.
   *
   * delta --|
   * |       | meet
   * res ----|
   *
   * @param delta approximation for a number steps "before"
   * @param res approximation for a complete sub-graph or also for "delta"
   * @return
   */
  def meet(delta: StepsResult, res: ExecutionResult): ExecutionResult = (delta, res) match {
    case (NPE, _) => NPE
    case (_, NPE) => NPE
    case (_, Error) => Error
    case (Identity, _) => res
    case (delta: ConditionalNPE, Return) => delta
    // current compromise between "complexity" of the method and "the profit of more complex method"
    // the only `@NotNull` that will not be inferred in this case is
    // data.InferenceData.compromise - this is pathological example
    // Also, this works for the formula "there should be at leas one finite path".
    case (ConditionalNPE(_), Cycle) => Cycle
    case (ConditionalNPE(e1), ConditionalNPE(e2)) => ConditionalNPE(SoP.meet(e1, e2))
  }


  /**
   *
   * Combines approximation of two subpaths. Note that delta2 corresponds to
   * a subpath, not to a complete subgraph. Used for combining local results of @NotNull parameter analysis.
   *
   * delta1 ----|
   * |          | subMeet
   * delta2 ----|
   * |
   * delta3
   * |
   * ...
   *
   * @param delta approximation for the first subpath
   * @param effect approximation for the second subpath
   * @return
   */
  def subMeet(delta: StepsResult, effect: InstructionEffect): StepsResult = (delta, effect) match {
    case (_, NoEffect) =>
      delta
    case (_, NpeEffect) =>
      NPE
    case (NPE, _) =>
      NPE
    case (Identity, LeakingEffect(product)) =>
      ConditionalNPE(Set(product))
    case (ConditionalNPE(sop), LeakingEffect(product)) =>
      ConditionalNPE(SoP.meet(sop, Set(product)))
  }
}

object NotNullParameterConstraint {
  // (taken: Boolean, hasCompanions: Boolean)
  val TAKEN = 1 // 1 << 0
  val HAS_COMPANIONS = 2 //1 << 1

  // (x != null) / (x instanceOf ..) was proceeded
  def isTaken(constraint: Int) = (constraint & TAKEN) != 0

  // some previous configuration is foo(param) -
  // hasCompanions = true means that it is possible indirect dereference
  def hasCompanions(constraint: Int) = (constraint & HAS_COMPANIONS) != 0
}

object NotNullParameterAnalysis {
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
  case class MakeResult(states: List[State], subResult: StepsResult, indices: List[Int]) extends PendingAction

  /**
   * Reusable pending list (pending stack) for push/pop actions during analyses.
   * @see faba.parameters.NotNullInAnalysis#pending
   */
  val sharedPendingStack = new Array[PendingAction](stepsLimit)

  /**
   * Reusable storage of sub results during analyses.
   * @see faba.parameters.NotNullInAnalysis#results
   */
  val sharedResults = new Array[ExecutionResult](stepsLimit)
}

class NotNullParameterAnalysis(val context: Context, val direction: Direction) extends StagedScAnalysis[Return.type] {
  import NotNullParameterAnalysis._
  import context._

  val results = NotNullParameterAnalysis.sharedResults
  val pending = NotNullParameterAnalysis.sharedPendingStack

  def combineResults(delta: StepsResult, subResults: List[ExecutionResult]): ExecutionResult =
    ExecutionResult.meet(delta, subResults.reduce(ExecutionResult.join))

  override def mkEquation(ret: Return.type): Equation[Key, Value] =
    Equation(aKey, Final(Values.Top))

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

    earlyResult match {
      case Some(ret) =>
        mkEquation(ret)
      case None =>
        Equation(aKey, results(0).toResult)
    }
  }

  override def processState(fState: State): Unit = {
    import faba.analysis.AnalysisUtils.popValue

    var state = fState
    var states: List[State] = Nil
    var subResult: StepsResult = Identity

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
        results(stateIndex) = Cycle
        computed(insnIndex) = state :: computed(insnIndex)
        if (states.nonEmpty)
          pendingPush(MakeResult(states, subResult, List(stateIndex)))
        return
      }

      val frame = conf.frame
      val insnNode = methodNode.instructions.get(insnIndex)
      val nextHistory = if (dfsTree.loopEnters(insnIndex)) conf :: history else history
      val (nextFrame, localEffect) = execute(frame, insnNode)

      // local "summing"
      val subResult2 = ExecutionResult.subMeet(subResult, localEffect)
      // if there was a switch in "current subresult" we need explicitly mark this
      val noSwitch = subResult == subResult2
      subResult = subResult2

      if (localEffect == NpeEffect) {
        // npe was detected, storing this fact for further analyses
        npe = true
        results(stateIndex) = NPE
        computed(insnIndex) = state :: computed(insnIndex)
        pendingPush(MakeResult(states, subResult, List(stateIndex)))
        return
      }

      val constraint = state.constraint

      val companionsNow =
        if (localEffect != NoEffect) NotNullParameterConstraint.HAS_COMPANIONS else 0
      val constraint1 =
        constraint | companionsNow

      insnNode.getOpcode match {
        case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
          if (!NotNullParameterConstraint.hasCompanions(constraint)) {
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
        case ATHROW if NotNullParameterConstraint.isTaken(constraint) =>
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

  private def execute(frame: Frame[BasicValue], insnNode: AbstractInsnNode): (Frame[BasicValue], InstructionEffect) = insnNode.getType match {
    case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
      (frame, NoEffect)
    case _ =>
      val nextFrame = new Frame(frame)
      NonNullInterpreter.reset()
      nextFrame.execute(insnNode, NonNullInterpreter)
      (nextFrame, NonNullInterpreter.getSubResult)
  }
}

object NullableParameterConstraint {
  val TAKEN = 1
  val NOT_TAKEN = 0
}

object NullableParameterAnalysis {
  val sharedPendingStack = new Array[State](stepsLimit)
}

/**
 *
 * @param context context of analysis
 * @param direction direction (In(i))
 */
class NullableParameterAnalysis(val context: Context, val direction: Direction) extends StagedScAnalysis[NPE.type] {

  import context._
  val pending = NullableParameterAnalysis.sharedPendingStack

  override def mkEquation(npe: NPE.type): Equation[Key, Value] =
    Equation(aKey, Final(Values.Top))

  private var leakedParameters: Set[Key] = Set()

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

    // either NPE was detected or some parameters leaked
    earlyResult match {
      case Some(npe) =>
        mkEquation(npe)
      case None =>
        // no parameter leaked ==> @Nullable
        if (leakedParameters.isEmpty)
          Equation(aKey, Final(Values.Null))
        else
          Equation(aKey, Pending(leakedParameters.map(key => Product(Values.Top, Set(key)))))
    }
  }

  override def processState(fState: State): Unit = {
    import faba.analysis.AnalysisUtils.popValue

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
        // Identity, changes nothing
        return

      val taken = state.constraint
      val frame = conf.frame
      val insnNode = methodNode.instructions.get(insnIndex)
      val nextHistory = if (isLoopEnter) conf :: history else history
      val (nextFrame, localSubResult) = execute(frame, insnNode)

      localSubResult match {
        case NpeEffect =>
          earlyResult = Some(NPE)
          return
        case LeakingEffect(keys) =>
          leakedParameters = leakedParameters ++ keys
        case NoEffect => //
          // nothing
      }

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

  // TODO - move into interpreter
  private def execute(frame: Frame[BasicValue], insnNode: AbstractInsnNode): (Frame[BasicValue], InstructionEffect) = insnNode.getType match {
    case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
      (frame, NoEffect)
    case _ =>
      val nextFrame = new Frame(frame)
      NullableInterpreter.reset()
      nextFrame.execute(insnNode, NullableInterpreter)
      (nextFrame, NullableInterpreter.getSubResult)
  }
}

/**
 * Effect of executing a single bytecode instruction.
 * Used for @NotNull parameter analysis and @Nullable parameter analysis.
 * Instruction effects have some subtle differences for @NotNull and @Nullable analyses.
 */
sealed trait InstructionEffect

/**
 * Nothing interested happens for parameter analysis.
 */
case object NoEffect extends InstructionEffect

/**
 * Execution result in NPE (with different semantics):
 * 1. Real NPE for @NotNull parameter analysis
 * 2. Real NPE or possible NPE (storing result somewhere) for @Nullable parameter analysis.
 */
case object NpeEffect extends InstructionEffect

/**
 * During execution of an instruction a parameter became an argument of other call.
 *
 * @param keys parameters (of other methods) to which a parameter in question is passed (leaked)
 */
case class LeakingEffect(keys: Set[Key]) extends InstructionEffect

abstract class Interpreter extends BasicInterpreter {
  val nullable: Boolean
  protected var _subResult: InstructionEffect = NoEffect
  final def reset(): Unit = {
    _subResult = NoEffect
  }

  def combine(res1: InstructionEffect, res2: InstructionEffect): InstructionEffect = (res1, res2) match {
    case (NoEffect, _) => res2
    case (_, NoEffect) => res1
    case (NpeEffect, _) => NpeEffect
    case (_, NpeEffect) => NpeEffect
    case (LeakingEffect(keys1), LeakingEffect(keys2)) => LeakingEffect(keys1 ++ keys2)
  }

  def getSubResult: InstructionEffect =
    _subResult

  final override def unaryOperation(insn: AbstractInsnNode, value: BasicValue): BasicValue = {
    insn.getOpcode match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER if value.isInstanceOf[ParamValue] =>
        _subResult = NpeEffect
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
        _subResult = NpeEffect
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD if v1.isInstanceOf[ParamValue] =>
        _subResult = NpeEffect
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  final override def ternaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue, v3: BasicValue): BasicValue = {
    insn.getOpcode match {
      case IASTORE | LASTORE | FASTORE | DASTORE | BASTORE | CASTORE | SASTORE
        if v1.isInstanceOf[ParamValue] =>
        _subResult = NpeEffect
      case AASTORE
        if v1.isInstanceOf[ParamValue] || (nullable && v3.isInstanceOf[ParamValue]) =>
        _subResult = NpeEffect
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  final override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    val static = opCode == INVOKESTATIC
    val shift = if (static) 0 else 1
    if ((opCode == INVOKESPECIAL || opCode == INVOKEINTERFACE || opCode == INVOKEVIRTUAL) && values.get(0).isInstanceOf[ParamValue]) {
      _subResult = NpeEffect
    }
    if (nullable && opCode == INVOKEINTERFACE) {
      for (i <- shift until values.size()) {
        if (values.get(i).isInstanceOf[ParamValue]) {
          _subResult = NpeEffect
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
            _subResult = combine(_subResult, LeakingEffect(Set(Key(method, In(i - shift), stable))))
          }
        }
      case _ =>
    }
    super.naryOperation(insn, values)
  }
}

object NonNullInterpreter extends Interpreter {
  override val nullable = false
}

object NullableInterpreter extends Interpreter {
  override val nullable = true
}
