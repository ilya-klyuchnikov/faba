package faba.asm.nullableResult

import faba.analysis.NullValue
import faba.data._
import faba.engine._
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.analysis.{Analyzer, BasicInterpreter, BasicValue}
import org.objectweb.asm.tree.{MethodNode, AbstractInsnNode, MethodInsnNode}
import org.objectweb.asm.{Opcodes, Type}
case class Calls(keys: Set[Key]) extends BasicValue(NullableResultInterpreter.ObjectType)

object NullableResultAnalysis {
  def analyze(className: String, methodNode: MethodNode): Result[Key, Value] = {
    val frames =
      new Analyzer[BasicValue](NullableResultInterpreter).analyze(className, methodNode)
    val insns = methodNode.instructions
    var result = BasicValue.REFERENCE_VALUE
    for (i <- 0 until frames.length) {
      val frame = frames(i)
      if (frame != null && insns.get(i).getOpcode == Opcodes.ARETURN) {
        result = combine(result, frame.pop())
      }
    }
    mkEquation(result)
  }

  def combine(v1: BasicValue, v2: BasicValue): BasicValue = (v1, v2) match {
    case (NullValue(), _) =>
      NullValue()
    case (_, NullValue()) =>
      NullValue()
    case (Calls(keys1), Calls(keys2)) =>
      Calls(keys1 ++ keys2)
    case (Calls(_), _) =>
      v1
    case (_, Calls(_)) =>
      v2
    case _ =>
      BasicValue.REFERENCE_VALUE
  }

  def mkEquation(v: BasicValue): Result[Key, Value] = v match {
    case NullValue() =>
      Final(Values.Null)
    case _ =>
      Final(Values.Bot)
  }
}

object NullableResultInterpreter extends BasicInterpreter {
  val ObjectType = Type.getObjectType("java/lang/Object")
  override def newOperation(insn: AbstractInsnNode): BasicValue =
    if (insn.getOpcode == Opcodes.ACONST_NULL)
      NullValue()
    else
      super.newOperation(insn)

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL =>
        val stable = opCode == INVOKESTATIC || opCode == INVOKESPECIAL
        val mNode = insn.asInstanceOf[MethodInsnNode]
        val method = Method(mNode.owner, mNode.name, mNode.desc)
        val retType = Type.getReturnType(mNode.desc)
        val isRefRetType = retType.getSort == Type.OBJECT || retType.getSort == Type.ARRAY
        if (isRefRetType)
          return Calls(Set(Key(method, Out, stable)))
      case _ =>
    }
    super.naryOperation(insn, values)
  }

  override def merge(v1: BasicValue, v2: BasicValue): BasicValue = (v1, v2) match {
    case (NullValue(), _) =>
      NullValue()
    case (_, NullValue()) =>
      NullValue()
    case (Calls(keys1), Calls(keys2)) =>
      Calls(keys1 ++ keys2)
    case (Calls(_), _) =>
      v1
    case (_, Calls(_)) =>
      v2
    case _ =>
      super.merge(v1, v2)
  }
}
