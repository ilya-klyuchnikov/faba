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
case class ConditionalNPE(sop: SoP) extends Result

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

class NotNullInAnalysis(val richControlFlow: RichControlFlow, val direction: Direction, val stable: Boolean) extends Analysis[Result] {

  override val identity: Result = Identity

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

  var id = 0

  override def processState(fState: State): Unit = {

    var state = fState
    var states: List[State] = Nil
    var subResult = identity

    while (true) {
      computed(state.conf.insnIndex).find(prevState => stateEquiv(state, prevState)) match {
        case Some(ps) =>
          results = results + (state.index -> results(ps.index))
          if (states.nonEmpty)
            pending.push(MakeResult(states, subResult, List(ps.index)))
          return
        case None =>
      }


      val stateIndex = state.index
      val conf = state.conf
      val insnIndex = conf.insnIndex
      val history = state.history

      val fold = dfsTree.loopEnters(insnIndex) && history.exists(prevConf => confInstance(conf, prevConf))

      if (fold) {
        results = results + (stateIndex -> identity)
        computed = computed.updated(insnIndex, state :: computed(insnIndex))
        if (states.nonEmpty)
          pending.push(MakeResult(states, subResult, List(stateIndex)))
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
        results = results + (stateIndex -> NPE)
        computed = computed.updated(insnIndex, state :: computed(insnIndex))
        pending.push(MakeResult(states, subResult, List(stateIndex)))
        return
      }

      insnNode.getOpcode match {
        case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
          if (!hasCompanions) {
            earlyResult = Some(Return)
            return
          } else {
            results = results + (stateIndex -> Return)
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
            // important to put subResult
            if (states.nonEmpty)
              pending.push(MakeResult(states, subResult, List(stateIndex)))
            return
          }
        case ATHROW if taken =>
          results = results + (stateIndex -> NPE)
          computed = computed.updated(insnIndex, state :: computed(insnIndex))
          if (states.nonEmpty)
            pending.push(MakeResult(states, subResult, List(stateIndex)))
          return
        case ATHROW =>
          results = results + (stateIndex -> Error)
          computed = computed.updated(insnIndex, state :: computed(insnIndex))
          if (states.nonEmpty)
            pending.push(MakeResult(states, subResult, List(stateIndex)))
          return
        case IFNONNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = insnIndex + 1
          val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult)
          states = state :: states
          state = nextState
        case IFNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult)
          states = state :: states
          state = nextState
        case IFEQ if popValue(frame).isInstanceOf[InstanceOfCheckValue] =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult)
          states = state :: states
          state = nextState
        case IFNE if popValue(frame).isInstanceOf[InstanceOfCheckValue] =>
          val nextInsnIndex = insnIndex + 1
          val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult)
          states = state :: states
          state = nextState
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
              State({id += 1; id}, Conf(nextInsnIndex, nextFrame1), nextHistory, taken, hasCompanions || notEmptySubResult)
          }
          states = state :: states
          if (nextStates.size == 1 && noSwitch) {
            state = nextStates.head
            //pending.push(MakeResult(states, subResult, List(state.index)))
            //pending.push(ProceedState(state))
            //return
          } else {
            pending.push(MakeResult(states, subResult, nextStates.map(_.index)))
            pending.pushAll(nextStates.map(s => ProceedState(s)))
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

// if everything is return, then parameter is nullable
class NullableInAnalysis(val richControlFlow: RichControlFlow, val direction: Direction, val stable: Boolean) extends Analysis[Result] {

  override val identity: Result = Identity

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

  var id = 0

  override def processState(fState: State): Unit = {

    var state = fState
    var states: List[State] = Nil
    var subResult = identity

    while (true) {
      computed(state.conf.insnIndex).find(prevState => stateEquiv(state, prevState)) match {
        case Some(ps) =>
          results = results + (state.index -> results(ps.index))
          if (states.nonEmpty)
            pending.push(MakeResult(states, subResult, List(ps.index)))
          return
        case None =>
      }

      val stateIndex = state.index
      val conf = state.conf
      val insnIndex = conf.insnIndex
      val history = state.history

      val fold = dfsTree.loopEnters(insnIndex) && history.exists(prevConf => confInstance(conf, prevConf))

      if (fold) {
        results = results + (stateIndex -> identity)
        computed = computed.updated(insnIndex, state :: computed(insnIndex))
        if (states.nonEmpty)
          pending.push(MakeResult(states, subResult, List(stateIndex)))
        return
      }

      val taken = state.taken
      val frame = conf.frame
      val insnNode = methodNode.instructions.get(insnIndex)
      val nextHistory = if (dfsTree.loopEnters(insnIndex)) conf :: history else history
      val (nextFrame, localSubResult) = execute(frame, insnNode)

      if (localSubResult == NPE) {
        earlyResult = Some(NPE)
        return
      }

      val subResult2 = Result.combineNullable(subResult, localSubResult)
      val noSwitch = subResult == subResult2
      subResult = subResult2

      insnNode.getOpcode match {
        case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
          if (insnNode.getOpcode == ARETURN && popValue(frame).isInstanceOf[ParamValue]) {
            earlyResult = Some(NPE)
            return
          }
          results = results + (stateIndex -> Return)
          computed = computed.updated(insnIndex, state :: computed(insnIndex))
          // important to put subResult
          if (states.nonEmpty)
            pending.push(MakeResult(states, subResult, List(stateIndex)))
          return
        case ATHROW if taken =>
          earlyResult = Some(NPE)
          return
        case ATHROW =>
          results = results + (stateIndex -> Error)
          computed = computed.updated(insnIndex, state :: computed(insnIndex))
          if (states.nonEmpty)
            pending.push(MakeResult(states, subResult, List(stateIndex)))
          return
        case IFNONNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = insnIndex + 1
          val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
          states = state :: states
          state = nextState
        case IFNULL if popValue(frame).isInstanceOf[ParamValue] =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
          states = state :: states
          state = nextState
        case IFEQ if popValue(frame).isInstanceOf[InstanceOfCheckValue] =>
          val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
          val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
          states = state :: states
          state = nextState
        case IFNE if popValue(frame).isInstanceOf[InstanceOfCheckValue] =>
          val nextInsnIndex = insnIndex + 1
          val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true, false)
          states = state :: states
          state = nextState
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
              State({id += 1; id}, Conf(nextInsnIndex, nextFrame1), nextHistory, taken, false)
          }
          states = state :: states
          if (nextStates.size == 1 && noSwitch) {
            state = nextStates.head
          } else {
            pending.push(MakeResult(states, subResult, nextStates.map(_.index)))
            pending.pushAll(nextStates.map(s => ProceedState(s)))
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
  protected var _subResult: Result = Identity
  def reset(): Unit = {
    _subResult = Identity
  }

  def combine(res1: Result, res2: Result): Result

  def getSubResult: Result =
    _subResult

  override def unaryOperation(insn: AbstractInsnNode, value: BasicValue): BasicValue = {
    insn.getOpcode match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER if value.isInstanceOf[ParamValue] =>
        _subResult = NPE
      case CHECKCAST if value.isInstanceOf[ParamValue] =>
        return new ParamValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc))
      case INSTANCEOF if value.isInstanceOf[ParamValue] =>
        return InstanceOfCheckValue()
      case _ =>
    }
    super.unaryOperation(insn, value)
  }

  override def binaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue): BasicValue = {
    insn.getOpcode match {
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD | PUTFIELD
        if v1.isInstanceOf[ParamValue] =>
        _subResult = NPE
      case _ =>

    }
    super.binaryOperation(insn, v1, v2)
  }

  override def ternaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue, v3: BasicValue): BasicValue = {
    insn.getOpcode match {
      case IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE
        if v1.isInstanceOf[ParamValue] =>
        _subResult = NPE
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }
}

object NonNullInterpreter extends Interpreter {
  override def combine(res1: Result, res2: Result): Result = Result.meet(res1, res2)

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    val static = opCode == INVOKESTATIC
    val shift = if (static) 0 else 1
    if ((opCode == INVOKESPECIAL || opCode == INVOKEINTERFACE || opCode == INVOKEVIRTUAL) && values.get(0).isInstanceOf[ParamValue]) {
      _subResult = NPE
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

object NullableInterpreter extends Interpreter {
  override def combine(res1: Result, res2: Result): Result = Result.join(res1, res2)

  override def binaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue): BasicValue = {
    insn.getOpcode match {
      case PUTFIELD
        if v1.isInstanceOf[ParamValue] || v2.isInstanceOf[ParamValue] =>
        _subResult = NPE
      case _ =>

    }
    super.binaryOperation(insn, v1, v2)
  }

  override def ternaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue, v3: BasicValue): BasicValue = {
    insn.getOpcode match {
      case AASTORE
        if v1.isInstanceOf[ParamValue] || v3.isInstanceOf[ParamValue] =>
        _subResult = NPE
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    val static = opCode == INVOKESTATIC
    val shift = if (static) 0 else 1
    if ((opCode == INVOKESPECIAL || opCode == INVOKEINTERFACE || opCode == INVOKEVIRTUAL) && values.get(0).isInstanceOf[ParamValue]) {
      _subResult = NPE
    }
    opCode match {
      // TODO - if is passed into INVOKEINTERFACE - we cannot say that it is @Nullable = top
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL | INVOKEINTERFACE =>
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
