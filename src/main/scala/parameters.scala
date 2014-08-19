package faba.parameters

import org.objectweb.asm.Type
import org.objectweb.asm.tree.analysis.{BasicInterpreter, Frame, BasicValue}
import org.objectweb.asm.tree.{MethodInsnNode, TypeInsnNode, JumpInsnNode, AbstractInsnNode}
import org.objectweb.asm.Opcodes._

import faba.analysis._
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
  import Analysis._
  val myArray = new Array[Result](LimitReachedException.limit)
  val myPending = new Array[PendingAction[Result]](LimitReachedException.limit)
  var notNullEarly: Long = 0
  var nullableEarly: Long = 0
  var notIdle: Long = 0
  var makeResult: Long = 0
}

class NullityInAnalysis(val richControlFlow: RichControlFlow, val direction: Direction, val stable: Boolean) extends Analysis[Result] {
  import Analysis._

  override val identity: Result = Identity
  val results = ParametersAnalysis.myArray
  val pending = ParametersAnalysis.myPending

  override def combineResults(delta: Result, subResults: List[Result]): Result =
    Result.meet(delta, subResults.reduce(Result.join))

  def mkNotNullEquation(result: Result): Equation[Key, Value] = result match {
    case Identity | Return | Error => Equation(aKey, Final(Values.Top))
    case NPE => Equation(aKey, Final(Values.NotNull))
    case ConditionalNPE(cnf) =>
      Equation(aKey, Pending(cnf.map(p => Component(Values.Top, p))))
  }

  def mkNullableEquation(result: Result): Equation[Key, Value] = result match {
    case NPE => Equation(aKey, Final(Values.Top))
    case Identity | Return | Error => Equation(aKey, Final(Values.Null))
    case ConditionalNPE(cnf) =>
      Equation(aKey, Pending(cnf.map(p => Component(Values.Top, p))))
  }

  override def isEarlyResult(res: Result): Boolean =
    false

  private var pendingTop: Int = 0

  private var earlyResultNotNull: Option[Result] = None
  private var earlyResultNullable: Option[Result] = None

  private var nullableResult = identity

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

  def analyze() {
    pendingPush(ProceedState(createStartState()))

    while (pendingTop > 0 && (earlyResultNotNull.isEmpty || earlyResultNullable.isEmpty)) pendingPop() match {
      case MakeResult(states, delta, subIndices) =>
        if (earlyResultNotNull.isEmpty) {
          val result = combineResults(delta, subIndices.map(results))
          // updating all results
          for (state <- states) {
            val insnIndex = state.conf.insnIndex
            results(state.index) = result
            computed(insnIndex) = state :: computed(insnIndex)
          }
        } else {
          ParametersAnalysis.makeResult += 1
        }
      case ProceedState(state) =>
        if (earlyResultNotNull.isDefined) {
          ParametersAnalysis.notNullEarly += 1
        }
        else if (earlyResultNullable.isDefined) {
          ParametersAnalysis.nullableEarly += 1
        } else {
          ParametersAnalysis.notIdle += 1
        }
        processState(state)
    }
  }

  def mkNotNullEquation: Equation[Key, Value] =
    mkNotNullEquation(earlyResultNotNull.getOrElse(results(0)))

  def mkNullableEquation: Equation[Key, Value] =
    mkNullableEquation(earlyResultNullable.getOrElse(nullableResult))

  var top = false
  var localSubResultNotNull: Result = identity
  var localSubResultNullable: Result = identity

  override def processState(fState: State): Unit = {

    var state = fState
    var states: List[State] = Nil
    var subResult = identity

    while (true) {
      computed(state.conf.insnIndex).find(prevState => stateEquiv(state, prevState)) match {
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

      val fold = dfsTree.loopEnters(insnIndex) && history.exists(prevConf => confInstance(conf, prevConf))
      computed(insnIndex) = state :: computed(insnIndex)

      if (fold) {
        results(stateIndex) = identity
        computed(insnIndex) = state :: computed(insnIndex)
        if (states.nonEmpty)
          pendingPush(MakeResult(states, subResult, List(stateIndex)))
        return
      }

      val taken = state.taken
      val frame = conf.frame
      val insnNode = methodNode.instructions.get(insnIndex)
      val nextHistory = if (dfsTree.loopEnters(insnIndex)) conf :: history else history
      val hasCompanions = state.hasCompanions

      val nextFrame = execute(frame, insnNode)
      val notEmptySubResultNotNull = localSubResultNotNull != Identity
      // local "summing"
      val subResult2 = Result.subMeet(subResult, localSubResultNotNull)
      val noSwitch = subResult == subResult2
      subResult = subResult2

      if (localSubResultNotNull == NPE) {
        results(stateIndex) = NPE
        pendingPush(MakeResult(states, subResult, List(stateIndex)))
      }

      if (localSubResultNullable == NPE || top) {
        earlyResultNullable = Some(NPE)
      }

      if (localSubResultNullable.isInstanceOf[ConditionalNPE]) {
        nullableResult = Result.combineNullable(nullableResult, localSubResultNullable)
      }

      insnNode.getOpcode match {
        case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
          if (!hasCompanions) {
            // there was no conditionals
            earlyResultNotNull = Some(Return)
          } else {
            results(stateIndex) = Return
            // important to put subResult
            if (states.nonEmpty)
              pendingPush(MakeResult(states, subResult, List(stateIndex)))
          }
          if (insnNode.getOpcode == ARETURN && popValue(frame).isInstanceOf[ParamValue]) {
            earlyResultNullable = Some(NPE)
          }
          return
        case ATHROW if taken =>
          results(stateIndex) = NPE
          if (states.nonEmpty)
            pendingPush(MakeResult(states, subResult, List(stateIndex)))
          earlyResultNullable = Some(NPE)
          return
        case ATHROW =>
          results(stateIndex) = Error
          if (states.nonEmpty)
            pendingPush(MakeResult(states, subResult, List(stateIndex)))
          return
        case IFNONNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = insnIndex + 1
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResultNotNull)
          states = state :: states
          state = nextState
        case IFNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResultNotNull)
          states = state :: states
          state = nextState
        case IFEQ if popValue(frame).isInstanceOf[InstanceOfCheckValue] =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResultNotNull)
          states = state :: states
          state = nextState
        case IFNE if popValue(frame).isInstanceOf[InstanceOfCheckValue] =>
          val nextInsnIndex = insnIndex + 1
          val nextState = State(mkId(), Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResultNotNull)
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
              State(mkId(), Conf(nextInsnIndex, nextFrame1), nextHistory, taken, hasCompanions || notEmptySubResultNotNull)
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

  private def execute(frame: Frame[BasicValue], insnNode: AbstractInsnNode): Frame[BasicValue] = insnNode.getType match {
    case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
      localSubResultNotNull = identity
      localSubResultNullable = identity
      top = false
      frame
    case _ =>
      NullityInterpreter.reset()
      val nextFrame = new Frame(frame)
      nextFrame.execute(insnNode, NullityInterpreter)
      localSubResultNotNull = NullityInterpreter.getNotSubResult
      localSubResultNullable = NullityInterpreter.getNullableSubResult
      top = NullityInterpreter.top
      nextFrame
  }

}

object NullityInterpreter extends BasicInterpreter {
  var top = false
  var _notNullSubResult: Result = Identity
  var _nullableSubResult: Result = Identity
  final def reset(): Unit = {
    _notNullSubResult = Identity
    _nullableSubResult = Identity
    top = false
  }

  def notNullCombine(res1: Result, res2: Result): Result = Result.meet(res1, res2)
  def nullableCombine(res1: Result, res2: Result): Result = Result.join(res1, res2)

  def getNotSubResult: Result = _notNullSubResult
  def getNullableSubResult: Result = _nullableSubResult

  final override def unaryOperation(insn: AbstractInsnNode, value: BasicValue): BasicValue = {
    insn.getOpcode match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER if value.isInstanceOf[ParamValue] =>
        _notNullSubResult = NPE
        _nullableSubResult = NPE
      case CHECKCAST if value.isInstanceOf[ParamValue] =>
        return new ParamValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc))
      case INSTANCEOF if value.isInstanceOf[ParamValue] =>
        return InstanceOfCheckValue()
      case _ =>
    }
    super.unaryOperation(insn, value)
  }

  final override def binaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue): BasicValue = {
    insn.getOpcode match {
      case PUTFIELD =>
        if (v1.isInstanceOf[ParamValue]) {
          _notNullSubResult = NPE
          _nullableSubResult = NPE
        }
        if (v2.isInstanceOf[ParamValue]) {
          _nullableSubResult = NPE
        }
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD if v1.isInstanceOf[ParamValue] =>
        _notNullSubResult = NPE
        _nullableSubResult = NPE
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  final override def ternaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue, v3: BasicValue): BasicValue = {
    insn.getOpcode match {
      case IASTORE | LASTORE | FASTORE | DASTORE | BASTORE | CASTORE | SASTORE
        if v1.isInstanceOf[ParamValue] =>
        _notNullSubResult = NPE
        _nullableSubResult = NPE
      case AASTORE =>
        if (v1.isInstanceOf[ParamValue]) {
          _notNullSubResult = NPE
          _nullableSubResult = NPE
        }
        if (v3.isInstanceOf[ParamValue]) {
          _nullableSubResult = NPE
        }
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  final override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    val static = opCode == INVOKESTATIC
    val shift = if (static) 0 else 1
    if ((opCode == INVOKESPECIAL || opCode == INVOKEINTERFACE || opCode == INVOKEVIRTUAL) && values.get(0).isInstanceOf[ParamValue]) {
      _notNullSubResult = NPE
      _nullableSubResult = NPE
    }
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL | INVOKEINTERFACE =>
        val stable = opCode == INVOKESTATIC || opCode == INVOKESPECIAL
        val mNode = insn.asInstanceOf[MethodInsnNode]
        for (i <- shift until values.size()) {
          if (values.get(i).isInstanceOf[ParamValue]) {
            if (opCode == INVOKEINTERFACE) {
              top = true
            } else {
              val method = Method(mNode.owner, mNode.name, mNode.desc)
              val conditionalNPE = ConditionalNPE(Key(method, In(i - shift), stable))
              _notNullSubResult = notNullCombine(_notNullSubResult, conditionalNPE)
              _nullableSubResult = nullableCombine(_nullableSubResult, conditionalNPE)
            }
          }
        }
      case _ =>
    }
    super.naryOperation(insn, values)
  }
}
