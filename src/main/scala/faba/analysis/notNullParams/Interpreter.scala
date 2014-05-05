package faba.analysis.notNullParams

import org.objectweb.asm.tree.analysis.{BasicValue, BasicInterpreter}
import org.objectweb.asm.tree.{MethodInsnNode, TypeInsnNode, AbstractInsnNode}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.Type

sealed trait ParamUsage {
  def join(other: ParamUsage): ParamUsage
  def toResult: Result
}

object NoUsage extends ParamUsage {
  override def join(other: ParamUsage) = other
  override def toResult: Result = Bottom
}

object DeReference extends ParamUsage {
  override def join(other: ParamUsage) = DeReference
  override def toResult: Result = NPE
}

case class ExternalUsage(cnf: CNF) extends ParamUsage {
  override def join(other: ParamUsage): ParamUsage = other match {
    case NoUsage => this
    case DeReference => DeReference
    case other: ExternalUsage => join(other)
  }

  def join(other: ExternalUsage) = ExternalUsage(this.cnf join other.cnf)
  override def toResult: Result = ConditionalNPE(cnf)
}

object ExternalUsage {
  def apply(passing: Parameter): ExternalUsage = ExternalUsage(Set(Set(passing)))
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
        return InstanceOfCheckValue
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
            _usage = _usage join ExternalUsage(Parameter(mNode.owner, mNode.name, mNode.desc, i - shift))
          }
        }
      case _ =>
    }
    super.naryOperation(insn, values)
  }
}
