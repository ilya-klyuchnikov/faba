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

case object Return extends Result
case object NPE extends Result
case class ConditionalNPE(cnf: SoP) extends Result

object Result {

  def join(r1: Result, r2: Result): Result = (r1, r2) match {
    case (Identity, _) => r2
    case (_, Identity) => r1
    case (Return, _) => Return
    case (_, Return) => Return
    case (NPE, NPE) => NPE
    case (NPE, r2: ConditionalNPE) => r2
    case (r1: ConditionalNPE, NPE) => r1
    case (ConditionalNPE(e1), ConditionalNPE(e2)) => ConditionalNPE(e1 join e2)
  }

  def meet(r1: Result, r2: Result): Result = (r1, r2) match {
    case (Identity, _) => r2
    case (_, Identity) => r1
    case (Return, _) => r2
    case (_, Return) => r1
    case (NPE, _) => NPE
    case (_, NPE) => r2
    case (ConditionalNPE(e1), ConditionalNPE(e2)) => ConditionalNPE(e1 meet e2)
  }
}

class NotNullInAnalysis(val richControlFlow: RichControlFlow, val direction: Direction) extends Analysis[Result] {
  import Utils._

  override val identity: Result = Identity
  private val parameter = Key(method, direction)

  override def stateInstance(curr: State, prev: State): Boolean = {
    curr.taken == prev.taken &&
      Utils.isInstance(curr.conf, prev.conf) &&
      curr.history.size == prev.history.size &&
      (curr.history, prev.history).zipped.forall(Utils.isInstance)
  }

  override def confInstance(curr: Conf, prev: Conf): Boolean =
    isInstance(curr, prev)

  override def combineResults(delta: Result, subResults: List[Result]): Result =
    Result.meet(delta, subResults.reduce(Result.join))

  override def mkEquation(result: Result): Equation[Key, Value] = result match {
    case Identity | Return => Equation(parameter, Final(Values.Top))
    case NPE => Equation(parameter, Final(Values.NotNull))
    case ConditionalNPE(cnf) =>
      require(cnf.forall(_.nonEmpty))
      Equation(parameter, Pending(Values.NotNull, cnf.map(p => Component(false, p))))
  }

  override def isEarlyResult(res: Result): Boolean =
    false

  var id = 0

  override def processState(state: State): Unit = {
    val stateIndex = state.index
    val conf = state.conf
    val insnIndex = conf.insnIndex
    val history = state.history
    val taken = state.taken
    val frame = conf.frame
    val loopEnter = dfsTree.loopEnters(insnIndex)
    val insnNode = methodNode.instructions.get(insnIndex)
    val nextHistory = if (loopEnter) conf :: history else history
    val (nextFrame, subResult) = execute(frame, insnNode)
    val hasCompanions = state.hasCompanions
    val notEmptySubResult = subResult != Identity

    if (subResult == NPE) {
      results = results + (stateIndex -> NPE)
      computed = computed.updated(insnIndex, state :: computed(insnIndex))
    } else insnNode.getOpcode match {
      case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN | RETURN =>
        if (!hasCompanions) {
          earlyResult = Some(Return)
        } else {
          results = results + (stateIndex -> Return)
          computed = computed.updated(insnIndex, state :: computed(insnIndex))
        }
      case ATHROW if taken =>
        results = results + (stateIndex -> NPE)
        computed = computed.updated(insnIndex, state :: computed(insnIndex))
      case ATHROW =>
        results = results + (stateIndex -> Identity)
        computed = computed.updated(insnIndex, state :: computed(insnIndex))
      case IFNONNULL if popValue(frame).isInstanceOf[ParamValue] =>
        val nextInsnIndex = insnIndex + 1
        val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult)
        pending.push(MakeResult(state, subResult, List(nextState.index)))
        pending.push(ProceedState(nextState))
      case IFNULL if popValue(frame).isInstanceOf[ParamValue] =>
        val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
        val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult)
        pending.push(MakeResult(state, subResult, List(nextState.index)))
        pending.push(ProceedState(nextState))
      case IFEQ if popValue(frame).isInstanceOf[InstanceOfCheckValue] =>
        val nextInsnIndex = methodNode.instructions.indexOf(insnNode.asInstanceOf[JumpInsnNode].label)
        val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult)
        pending.push(MakeResult(state, subResult, List(nextState.index)))
        pending.push(ProceedState(nextState))
      case IFNE if popValue(frame).isInstanceOf[InstanceOfCheckValue] =>
        val nextInsnIndex = insnIndex + 1
        val nextState = State({id += 1; id}, Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult)
        pending.push(MakeResult(state, subResult, List(nextState.index)))
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
            State({id += 1; id}, Conf(nextInsnIndex, nextFrame1), nextHistory, taken, hasCompanions || notEmptySubResult)
        }
        pending.push(MakeResult(state, subResult, nextStates.map(_.index)))
        pending.pushAll(nextStates.map(s => ProceedState(s)))
    }
  }

  private def execute(frame: Frame[BasicValue], insnNode: AbstractInsnNode) = insnNode.getType match {
    case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
      (frame, Identity)
    case _ =>
      val nextFrame = new Frame(frame)
      Interpreter.reset()
      nextFrame.execute(insnNode, Interpreter)
      (nextFrame, Interpreter.getUsage.toResult)
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
    case _ =>
      true
  }

}

sealed trait ParamUsage {
  def meet(other: ParamUsage): ParamUsage
  def toResult: Result
}

// Nullable, Top
object NoUsage extends ParamUsage {
  override def meet(other: ParamUsage) = other
  override def toResult: Result = Identity
}

// NotNull, Bottom
object DeReference extends ParamUsage {
  override def meet(other: ParamUsage) = DeReference
  override def toResult: Result = NPE
}

case class ExternalUsage(cnf: SoP) extends ParamUsage {
  // intersect
  override def meet(other: ParamUsage): ParamUsage = other match {
    case NoUsage => this
    case DeReference => DeReference
    case other: ExternalUsage => join(other)
  }

  def join(other: ExternalUsage) = ExternalUsage(this.cnf meet other.cnf)
  override def toResult: Result = ConditionalNPE(cnf)
}

object ExternalUsage {
  def apply(passing: Key): ExternalUsage = ExternalUsage(Set(Set(passing)))
}

object Interpreter extends BasicInterpreter {
  private var _usage: ParamUsage = NoUsage
  def reset(): Unit = {
    _usage = NoUsage
  }

  def getUsage: ParamUsage =
    _usage

  override def unaryOperation(insn: AbstractInsnNode, value: BasicValue): BasicValue = {
    val opCode = insn.getOpcode
    opCode match {
      case GETFIELD | ARRAYLENGTH | MONITOREXIT if value.isInstanceOf[ParamValue] =>
        _usage = DeReference
      case CHECKCAST if value.isInstanceOf[ParamValue] =>
        return new ParamValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc))
      case INSTANCEOF if value.isInstanceOf[ParamValue] =>
        return InstanceOfCheckValue()
      case _ =>
    }
    super.unaryOperation(insn, value)
  }

  override def binaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue): BasicValue = {
    val opCode = insn.getOpcode
    opCode match {
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD | PUTFIELD
        if v1.isInstanceOf[ParamValue] =>
        _usage = DeReference
      case _ =>

    }
    super.binaryOperation(insn, v1, v2)
  }

  override def ternaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue, v3: BasicValue): BasicValue = {
    val opCode = insn.getOpcode
    opCode match {
      case IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE
        if v1.isInstanceOf[ParamValue] =>
        _usage = DeReference
      case _ =>

    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    val static = opCode == INVOKESTATIC
    val shift = if (static) 0 else 1
    if (opCode != MULTIANEWARRAY && !static && values.get(0).isInstanceOf[ParamValue]) {
      _usage = DeReference
    }
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL =>
        val mNode = insn.asInstanceOf[MethodInsnNode]
        for (i <- shift until values.size()) {
          if (values.get(i).isInstanceOf[ParamValue]) {
            val method = Method(mNode.owner, mNode.name, mNode.desc)
            _usage = _usage meet ExternalUsage(Key(method, In(i - shift)))
          }
        }
      case _ =>
    }
    super.naryOperation(insn, values)
  }
}
