package faba.analysis.nullableResult

import faba.analysis.AsmAbstractValue
import faba.asm._
import faba.calls.CallUtils
import faba.data._
import faba.engine._

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree._
import org.objectweb.asm.tree.analysis.{BasicInterpreter, BasicValue, Frame}
import org.objectweb.asm.{Opcodes, Type}

// this is significant to set magic type because of BasicObject#equals
@AsmAbstractValue case class LabeledNull(origins: Set[Int]) extends BasicValue(Type.getObjectType("null"))
@AsmAbstractValue case class Calls(keys: Set[Key]) extends BasicValue(NullableResultAnalysis.CallType) {
  override def toString = s"Calls(${keys.toString})"

  override def equals(value: scala.Any): Boolean = value match {
    case Calls(keys1) => keys == keys1
    case _ => false
  }

  override def hashCode(): Int =
    keys.hashCode()
}
@AsmAbstractValue case class ThisValue() extends BasicValue(NullableResultAnalysis.ObjectType) {
  override def equals(value: scala.Any) = value match {
    case ThisValue() => true
    case _ => false
  }

  override def hashCode() = 1
}
case class Constraint(calls: Set[Key], nulls: Set[Int])

object NullableResultAnalysis {
  val lNull = new LabeledNull(Set())
  val ObjectType = Type.getObjectType("java/lang/Object")
  val CallType = Type.getObjectType("/Call")
  def analyze(className: String, methodNode: MethodNode, origins: Array[Boolean], jsr: Boolean): Result[Key, Value] = {
    val insns = methodNode.instructions
    val data = new Array[Constraint](insns.size())

    val frames: Array[Frame[BasicValue]] =
      if (jsr)
        new AnalyzerExt[BasicValue, Constraint, NullableResultInterpreter](NullableResultInterpreter(insns, origins), data, Constraint(Set(), Set())).analyze("this", methodNode)
      else
        new LiteAnalyzerExt[BasicValue, Constraint, NullableResultInterpreter](NullableResultInterpreter(insns, origins), data, Constraint(Set(), Set())).analyze("this", methodNode)

    var result = BasicValue.REFERENCE_VALUE
    for (i <- 0 until frames.length) {
      val frame = frames(i)
      if (frame != null && insns.get(i).getOpcode == Opcodes.ARETURN) {
        val constraint = data(i)
        result = combine(result, frame.pop(), constraint)
      }
    }
    mkEquation(result)
  }

  // the second is new value
  def combine(v1: BasicValue, v2: BasicValue, constraint: Constraint): BasicValue = (v1, v2) match {
    case (LabeledNull(_), _) =>
      lNull
    case (_, LabeledNull(is)) =>
      val aliveNulls = is -- constraint.nulls
      if (aliveNulls.nonEmpty) lNull else v1
    case (Calls(keys1), Calls(keys2)) =>
      Calls(keys1 ++ (keys2 -- constraint.calls))
    case (Calls(_), _) =>
      v1
    case (_, Calls(keys)) =>
      Calls(keys -- constraint.calls)
    case _ =>
      BasicValue.REFERENCE_VALUE
  }

  def mkEquation(v: BasicValue): Result[Key, Value] = v match {
    case LabeledNull(_) =>
      Final(Values.Null)
    case Calls(keys) =>
      Pending[Key, Value](keys map { k => Product(Values.Null, Set(k)) })
    case _ =>
      Final(Values.Bot)
  }
}

case class NullableResultInterpreter(insns: InsnList, origins: Array[Boolean]) extends BasicInterpreter with InterpreterExt[Constraint] {
  var constraint: Constraint = null
  var delta: Set[Key] = null
  var nullsDelta: Set[Int] = null

  var notNullInsn: Option[Int] = None
  var notNullCall: Set[Key] = Set()
  var notNullNull: Set[Int] = Set()

  override def init(previous: Constraint) {
    constraint = previous
    delta = Set()
    nullsDelta = Set()

    notNullInsn = None
    notNullCall = Set()
    notNullNull = Set()
  }

  override def getAfterData(insn: Int): Constraint = {
    val notNull = Some(insn) == notNullInsn
    Constraint(
      constraint.calls ++ delta ++ (if (notNull) notNullCall else Set()),
      constraint.nulls ++ nullsDelta ++ (if (notNull) notNullNull else Set())
    )
  }

  override def newValue(tp: Type): BasicValue =
    if (tp != null && tp.toString == "Lthis;") ThisValue() else super.newValue(tp)

  override def newOperation(insn: AbstractInsnNode): BasicValue =
    if (insn.getOpcode == Opcodes.ACONST_NULL) {
      val insnIndex = insns.indexOf(insn)
      if (origins(insnIndex)) LabeledNull(Set(insnIndex)) else super.newOperation(insn)
    }
    else
      super.newOperation(insn)

  final override def unaryOperation(insn: AbstractInsnNode, value: BasicValue): BasicValue = {
    insn.getOpcode match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER if value.isInstanceOf[Calls] =>
        delta = value.asInstanceOf[Calls].keys
      case IFNULL if value.isInstanceOf[Calls] =>
        notNullInsn = Some(insns.indexOf(insn) + 1)
        notNullCall = value.asInstanceOf[Calls].keys
      case IFNULL if value.isInstanceOf[LabeledNull] =>
        notNullInsn = Some(insns.indexOf(insn) + 1)
        notNullNull = value.asInstanceOf[LabeledNull].origins
      case IFNONNULL if value.isInstanceOf[Calls] =>
        notNullInsn = Some(insns.indexOf(insn.asInstanceOf[JumpInsnNode].label))
        notNullCall = value.asInstanceOf[Calls].keys
      case IFNONNULL if value.isInstanceOf[LabeledNull] =>
        notNullInsn = Some(insns.indexOf(insn.asInstanceOf[JumpInsnNode].label))
        notNullNull = value.asInstanceOf[LabeledNull].origins
      case _ =>
    }
    super.unaryOperation(insn, value)
  }

  final override def binaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue): BasicValue = {
    insn.getOpcode match {
      case PUTFIELD | IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD =>
        v1 match {
          case Calls(keys) =>
            delta = keys
          case LabeledNull(is) =>
            nullsDelta = is
          case _ =>
        }
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  final override def ternaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue, v3: BasicValue): BasicValue = {
    insn.getOpcode match {
      case IASTORE | LASTORE | FASTORE | DASTORE | BASTORE | CASTORE | SASTORE | AASTORE =>
        v1 match {
          case Calls(keys) =>
            delta = keys
          case LabeledNull(is) =>
            nullsDelta = is
          case _ =>
        }
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    opCode match {
      case INVOKESPECIAL | INVOKEINTERFACE | INVOKEVIRTUAL | INVOKEDYNAMIC =>
        // handling dereferencing
        values.get(0) match {
          case Calls(keys) =>
            delta = keys
          case LabeledNull(is) =>
            nullsDelta = is
          case _ =>
        }
      case _ =>
    }
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL if origins(insns.indexOf(insn)) =>
        val resolveDir = CallUtils.callResolveDirection(opCode)
        val mNode = insn.asInstanceOf[MethodInsnNode]
        val method = Method(mNode.owner, mNode.name, mNode.desc)
        return Calls(Set(Key(method, Out, resolveDir)))
      case _ =>
    }
    super.naryOperation(insn, values)
  }

  override def merge(v1: BasicValue, v2: BasicValue): BasicValue = (v1, v2) match {
      case (LabeledNull(is1), LabeledNull(is2)) =>
        LabeledNull(is1 ++ is2)
      case (LabeledNull(_), _) =>
        v1
      case (_, LabeledNull(_)) =>
        v2
      case (Calls(keys1), Calls(keys2)) =>
        Calls(keys1 ++ keys2)
      case (Calls(_), _) =>
        v1
      case (_, Calls(_)) =>
        v2
      case _ =>
        super.merge(v1, v2)
  }

  // all keys that were dereferenced to this point
  override def merge(constraint1: Constraint, constraint2: Constraint): Constraint =
    Constraint(constraint1.calls ++ constraint2.calls, constraint1.nulls ++ constraint2.nulls)
}
