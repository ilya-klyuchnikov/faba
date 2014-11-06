package faba.analysis.resultInfluence

import faba.analysis.leakingParameters._
import faba.analysis.resultOrigins._

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.Type
import org.objectweb.asm.tree.analysis.{Frame, Interpreter}
import org.objectweb.asm.tree.{AbstractInsnNode, MethodNode}

object ResultInfluence {
  def analyze(methodNode: MethodNode, leaking: LeakingParameters, origins: Origins): Array[Boolean] = {
    val leakingParameters = origins.parameters
    val interpreter = new ResultInfluenceInterpreter(java.util.Arrays.copyOf(leakingParameters, leakingParameters.length))
    var i: Int = 0
    val insns = methodNode.instructions
    val frames = leaking.frames
    val originInsns = origins.instructions
    val maxInsnIndex = insns.size()
    while (i < maxInsnIndex) {
      if (originInsns(i)) {
        val insnNode = insns.get(i)
        val frame = frames(i)
        if (frame != null)
          insnNode.getOpcode match {
            case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL | INVOKEINTERFACE =>
              new Frame(frame).execute(insnNode, interpreter)
            case _ =>
          }
      }
      i += 1
    }
    interpreter.result
  }


}

class ResultInfluenceInterpreter(val result: Array[Boolean]) extends Interpreter[ParamsValue](ASM5) {
  val val1 = ParamsValue(Set(), 1)

  override def newValue(`type`: Type) = ???
  override def newOperation(insn: AbstractInsnNode) = ???
  override def binaryOperation(insn: AbstractInsnNode, value1: ParamsValue, value2: ParamsValue) = ???
  override def merge(v: ParamsValue, w: ParamsValue) = ???

  // we are interested only in this
  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: ParamsValue]): ParamsValue = {
    val opcode = insn.getOpcode
    opcode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL | INVOKEINTERFACE =>
        var n = if (opcode == INVOKESTATIC) 0 else 1
        while (n < values.size()) {
          for (i <- values.get(n).params)
            result(i) = true
          n += 1
        }
      case _ =>
    }
    val1
  }

  override def unaryOperation(insn: AbstractInsnNode, value: ParamsValue) = ???
  override def ternaryOperation(insn: AbstractInsnNode, value1: ParamsValue, value2: ParamsValue, value3: ParamsValue) = ???
  override def returnOperation(insn: AbstractInsnNode, value: ParamsValue, expected: ParamsValue) = ???
  override def copyOperation(insn: AbstractInsnNode, value: ParamsValue) = ???
}