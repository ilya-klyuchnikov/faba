package faba.analysis.nullBooleanContracts

import org.objectweb.asm.tree.analysis.{BasicValue, BasicInterpreter}
import org.objectweb.asm.tree.{MethodInsnNode, TypeInsnNode, AbstractInsnNode}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.Type

object Interpreter extends BasicInterpreter {
  override def newOperation(insn: AbstractInsnNode): BasicValue =
    insn.getOpcode match {
      case ICONST_0 =>
        FalseValue()
      case ICONST_1 =>
        TrueValue()
      case _ =>
        super.newOperation(insn)
    }

  override def unaryOperation(insn: AbstractInsnNode, value: BasicValue): BasicValue =
    insn.getOpcode match {
      case CHECKCAST if value.isInstanceOf[ParamValue] =>
        new ParamValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc))
      case INSTANCEOF if value.isInstanceOf[ParamValue] =>
        InstanceOfCheckValue()
      case _ =>
        super.unaryOperation(insn, value)
    }


  // TODO - here only the first param is taken into account (for simplicity)
  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    val static = opCode == INVOKESTATIC
    val shift = if (static) 0 else 1
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL =>
        val mNode = insn.asInstanceOf[MethodInsnNode]
        for (i <- shift until values.size()) {
          if (values.get(i).isInstanceOf[ParamValue]) {
            return CallResultValue(
              Type.getReturnType(insn.asInstanceOf[MethodInsnNode].desc),
              Parameter(mNode.owner, mNode.name, mNode.desc, i - shift)
            )
          }
        }
        super.naryOperation(insn, values)
      case _ =>
        super.naryOperation(insn, values)
    }
  }
}
