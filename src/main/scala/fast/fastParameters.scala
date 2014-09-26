package faba.fastParameters

import faba.asm.{FastFrame, FastValues, FastBasicInterpreter}
import org.objectweb.asm.tree.{MethodInsnNode, JumpInsnNode, AbstractInsnNode}
import org.objectweb.asm.Opcodes._

import faba.fastAnalysis.{Utils => FUtils, _}
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

object ParametersAnalysis {
  import FastAnalysis._
  val myArray = new Array[Result](LimitReachedException.limit)
  val myPending = new Array[PendingAction[Result]](LimitReachedException.limit)
  var executeTime: Long = 0
  var findEquivTime: Long = 0
}

class NotNullInFastAnalysis(val richControlFlow: RichControlFlow, val direction: Direction, val stable: Boolean) extends FastAnalysis[Result] {
  import FastAnalysis._

  override val identity: Result = Identity
  val results = ParametersAnalysis.myArray
  val pending = ParametersAnalysis.myPending

  override def combineResults(delta: Result, subResults: List[Result]): Result =
    Result.meet(delta, subResults.reduce(Result.join))

  override def mkEquation(result: Result): Equation[Key, Value] = result match {
    case Identity | Return | Error => Equation(aKey, Final(Values.Top))
    case NPE => Equation(aKey, Final(Values.NotNull))
    case ConditionalNPE(cnf) =>
      Equation(aKey, Pending(cnf.map(p => Component(Values.Top, p))))
  }

  override def isEarlyResult(res: Result): Boolean =
    false

  var npe = false

  private var pendingTop: Int = 0

  @inline
  final def pendingPush(action: PendingAction[Result]) {
    pending(pendingTop) = action
    pendingTop += 1
  }

  @inline
  final def pendingPop(): PendingAction[Result] = {
    pendingTop -= 1
    pending(pendingTop)
  }

  def analyze(): Equation[Key, Value] = {
    pendingPush(ProceedState(createStartState()))

    while (pendingTop > 0 && earlyResult.isEmpty) pendingPop() match {
      case MakeResult(states, delta, subIndices) =>
        val result = combineResults(delta, subIndices.map(results))
        if (isEarlyResult(result)) {
          earlyResult = Some(result)
        } else {
          // updating all results
          for (state <- states) {
            val insnIndex = state.conf.insnIndex
            results(state.index) = result
            addComputed(insnIndex, state)
          }
        }
      case ProceedState(state) =>
        processState(state)
    }

    mkEquation(earlyResult.getOrElse(results(0)))
  }

  def alreadyComputed(state: State): Option[Int] = {
    val start = System.nanoTime()
    var candidates = computed(state.conf.insnIndex)
    var already: Option[Int] = None
    if (candidates != null) {
      while (candidates.nonEmpty && already.isEmpty) {
        if (stateEquiv(state, candidates.head))
          already = Some(candidates.head.index)
        else
          candidates = candidates.tail
      }
    }
    ParametersAnalysis.findEquivTime += System.nanoTime() - start
    already
  }

  override def processState(fState: State): Unit = {

    var state = fState
    var states: List[State] = Nil
    var subResult = identity

    while (true) {

      alreadyComputed(state) match {
        case Some(psIndex) =>
          results(state.index) = results(psIndex)
          if (states.nonEmpty)
            pendingPush(MakeResult(states, subResult, psIndex :: Nil))
          return
        case None =>
      }

      val stateIndex = state.index
      val conf = state.conf
      val insnIndex = conf.insnIndex
      val history = state.history

      val fold = dfsTree.loopEnters(insnIndex) && FUtils.isFold(conf, history)

      if (fold) {
        results(stateIndex) = identity
        addComputed(insnIndex, state)
        if (states.nonEmpty)
          pendingPush(MakeResult(states, subResult, List(stateIndex)))
        return
      }

      val taken = state.taken
      val frame = conf.frame
      val insnNode = methodNode.instructions.get(insnIndex)
      val nextHistory = if (dfsTree.loopEnters(insnIndex)) conf :: history else history
      val hasCompanions = state.hasCompanions
      val (nextFrame, localSubResult) = execute(frame, insnNode)
      val notEmptySubResult = localSubResult != Identity

      // local "summing"
      val subResult2 = Result.subMeet(subResult, localSubResult)
      val noSwitch = subResult == subResult2
      subResult = subResult2

      if (localSubResult == NPE) {
        // npe was detected
        npe = true
        results(stateIndex) = NPE
        addComputed(insnIndex, state)
        pendingPush(MakeResult(states, subResult, stateIndex :: Nil))
        return
      }

      insnNode.getOpcode match {
        case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
          if (!hasCompanions) {
            earlyResult = Some(Return)
            return
          } else {
            results(stateIndex) = Return
            addComputed(insnIndex, state)
            // important to put subResult
            if (states.nonEmpty)
              pendingPush(MakeResult(states, subResult, List(stateIndex)))
            return
          }
        case ATHROW if taken =>
          results(stateIndex) = NPE
          npe = true
          addComputed(insnIndex, state)
          if (states.nonEmpty)
            pendingPush(MakeResult(states, subResult, List(stateIndex)))
          return
        case ATHROW =>
          results(stateIndex) = Error
          addComputed(insnIndex, state)
          if (states.nonEmpty)
            pendingPush(MakeResult(states, subResult, List(stateIndex)))
          return
        case IFNONNULL if popValue(frame) == FastValues.PARAM_VAL =>
          val nextInsnIndex = insnIndex + 1
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult)
          states = state :: states
          state = nextState
        case IFNULL if popValue(frame) == FastValues.PARAM_VAL =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult)
          states = state :: states
          state = nextState
        case IFEQ if popValue(frame) == FastValues.INSTANCE_OF_CHECK_VAL =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult)
          states = state :: states
          state = nextState
        case IFNE if popValue(frame) == FastValues.INSTANCE_OF_CHECK_VAL =>
          val nextInsnIndex = insnIndex + 1
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult)
          states = state :: states
          state = nextState
        case _ =>
          val nextInsnIndices = controlFlow.transitions(insnIndex)
          val nextStates = nextInsnIndices.map {
            nextInsnIndex =>
              val nextFrame1 = if (controlFlow.errors(nextInsnIndex) && controlFlow.errorTransitions(insnIndex -> nextInsnIndex)) {
                val handler = new FastFrame(frame)
                handler.clearStack()
                handler.push(FastValues.ANY_VAL)
                handler
              } else {
                nextFrame
              }
              State(mkId(), Conf(nextInsnIndex, nextFrame1), nextHistory, taken, hasCompanions || notEmptySubResult)
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

  private def execute(frame: FastFrame, insnNode: AbstractInsnNode) = {
    val start = System.nanoTime()
    val result = insnNode.getType match {
      case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
        (frame, Identity)
      case _ =>
        val nextFrame = new FastFrame(frame)
        NonNullInterpreter.reset()
        nextFrame.execute(insnNode, NonNullInterpreter)
        (nextFrame, NonNullInterpreter.getSubResult)
    }
    ParametersAnalysis.executeTime += System.nanoTime() - start
    result
  }

}

// if everything is return, then parameter is nullable
class NullableInFastAnalysis(val richControlFlow: RichControlFlow, val direction: Direction, val stable: Boolean) extends FastAnalysis[Result] {

  override val identity: Result = Identity
  val pending = FastAnalysis.ourPending

  override def combineResults(delta: Result, subResults: List[Result]): Result =
    Result.combineNullable(delta, subResults.reduce(Result.combineNullable))

  override def mkEquation(result: Result): Equation[Key, Value] = result match {
    case NPE => Equation(aKey, Final(Values.Top))
    case Identity | Return | Error => Equation(aKey, Final(Values.Null))
    case ConditionalNPE(cnf) =>
      Equation(aKey, Pending(cnf.map(p => Component(Values.Top, p))))
  }

  override def isEarlyResult(res: Result): Boolean =
    false

  private var myResult = identity

  private var pendingTop: Int = 0

  @inline
  final def pendingPush(state: State) {
    pending(pendingTop) = state
    pendingTop += 1
  }

  @inline
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

  def alreadyComputed(state: State): Boolean = {
    val start = System.nanoTime()
    var candidates = computed(state.conf.insnIndex)
    var already = false
    if (candidates != null) {
      while (!already && candidates.nonEmpty) {
        if (stateEquiv(state, candidates.head))
          already = true
        else
          candidates = candidates.tail
      }
    }
    ParametersAnalysis.findEquivTime += System.nanoTime() - start
    already
  }

  override def processState(fState: State): Unit = {

    var state = fState

    while (true) {
      if (alreadyComputed(state)) {
        return
      }

      val stateIndex = state.index
      val conf = state.conf
      val insnIndex = conf.insnIndex
      val history = state.history

      val isLoopEnter = dfsTree.loopEnters(insnIndex)
      val fold = isLoopEnter && FUtils.isFold(conf, history)

      addComputed(insnIndex, state)

      if (fold) {
        return
      }

      val taken = state.taken
      val frame = conf.frame
      val insnNode = methodNode.instructions.get(insnIndex)
      val nextHistory = if (isLoopEnter) conf :: history else history
      val (nextFrame, localSubResult, top) = execute(frame, insnNode)

      if (localSubResult == NPE || top) {
        earlyResult = Some(NPE)
        return
      }

      if (localSubResult.isInstanceOf[ConditionalNPE])
        myResult = Result.combineNullable(myResult, localSubResult)

      insnNode.getOpcode match {
        case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
          if (insnNode.getOpcode == ARETURN && popValue(frame) == FastValues.PARAM_VAL) {
            earlyResult = Some(NPE)
            return
          }
          return
        case ATHROW if taken =>
          earlyResult = Some(NPE)
          return
        case ATHROW =>
          return
        case IFNONNULL if popValue(frame) == FastValues.PARAM_VAL =>
          val nextInsnIndex = insnIndex + 1
          state = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
        case IFNULL if popValue(frame) == FastValues.PARAM_VAL =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          state = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
        case IFEQ if popValue(frame) == FastValues.INSTANCE_OF_CHECK_VAL =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          state = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
        case IFNE if popValue(frame) == FastValues.INSTANCE_OF_CHECK_VAL =>
          val nextInsnIndex = insnIndex + 1
          state = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
        case _ =>
          val nextInsnIndices = controlFlow.transitions(insnIndex)
          val nextStates = nextInsnIndices.map {
            nextInsnIndex =>
              val nextFrame1 = if (controlFlow.errors(nextInsnIndex) && controlFlow.errorTransitions(insnIndex -> nextInsnIndex)) {
                val handler = new FastFrame(frame)
                handler.clearStack()
                handler.push(FastValues.ANY_VAL)
                handler
              } else {
                nextFrame
              }
              State(mkId(), Conf(nextInsnIndex, nextFrame1), nextHistory, taken, false)
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

  private def execute(frame: FastFrame, insnNode: AbstractInsnNode) = {
    val start = System.nanoTime()
    val result = insnNode.getType match {
      case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
        (frame, Identity, false)
      case _ =>
        val nextFrame = new FastFrame(frame)
        NullableInterpreter.reset()
        nextFrame.execute(insnNode, NullableInterpreter)
        (nextFrame, NullableInterpreter.getSubResult, NullableInterpreter.top)
    }
    ParametersAnalysis.executeTime += System.nanoTime() - start
    result
  }

}

abstract class Interpreter extends FastBasicInterpreter {
  var top = false
  val nullable: Boolean
  protected var _subResult: Result = Identity
  final def reset(): Unit = {
    _subResult = Identity
    top = false
  }

  def combine(res1: Result, res2: Result): Result

  def getSubResult: Result =
    _subResult

  final override def unaryOperation(insn: AbstractInsnNode, value: Int): Int = {
    insn.getOpcode match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER if value == FastValues.PARAM_VAL =>
        _subResult = NPE
      case CHECKCAST if value == FastValues.PARAM_VAL =>
        return FastValues.PARAM_VAL
      case INSTANCEOF if value == FastValues.PARAM_VAL =>
        return FastValues.INSTANCE_OF_CHECK_VAL
      case _ =>
    }
    super.unaryOperation(insn, value)
  }

  final override def binaryOperation(insn: AbstractInsnNode, v1: Int, v2: Int): Int = {
    insn.getOpcode match {
      case PUTFIELD
        if (v1 == FastValues.PARAM_VAL) || (nullable && v2 == FastValues.PARAM_VAL) =>
        _subResult = NPE
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD if v1 == FastValues.PARAM_VAL =>
        _subResult = NPE
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  final override def ternaryOperation(insn: AbstractInsnNode, v1: Int, v2: Int, v3: Int): Int = {
    insn.getOpcode match {
      case IASTORE | LASTORE | FASTORE | DASTORE | BASTORE | CASTORE | SASTORE
        if v1 == FastValues.PARAM_VAL =>
        _subResult = NPE
      case AASTORE
        if v1 == FastValues.PARAM_VAL || (nullable && v3 == FastValues.PARAM_VAL) =>
        _subResult = NPE
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  final override def naryOperation(insn: AbstractInsnNode, values: Array[Int]): Int = {
    val opCode = insn.getOpcode
    val static = opCode == INVOKESTATIC
    val shift = if (static) 0 else 1
    if ((opCode == INVOKESPECIAL || opCode == INVOKEINTERFACE || opCode == INVOKEVIRTUAL) && values(0) == FastValues.PARAM_VAL) {
      _subResult = NPE
    }
    if (nullable && opCode == INVOKEINTERFACE) {
      var i = shift
      while (i < values.length) {
        if (values(i) == FastValues.PARAM_VAL) {
          top = true
          return super.naryOperation(insn, values)
        }
        i += 1
      }
      return super.naryOperation(insn, values)
    }
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL =>
        val stable = opCode == INVOKESTATIC || opCode == INVOKESPECIAL
        val mNode = insn.asInstanceOf[MethodInsnNode]
        var i = shift
        while (i < values.length) {
          if (values(i) == FastValues.PARAM_VAL) {
            val method = Method(mNode.owner, mNode.name, mNode.desc)
            _subResult = combine(_subResult, ConditionalNPE(Key(method, In(i - shift), stable)))
          }
          i += 1
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
