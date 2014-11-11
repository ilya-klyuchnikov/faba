package faba.analysis.resultInfluence

import faba.analysis.leakingParameters._
import faba.analysis.resultOrigins._

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.Type
import org.objectweb.asm.tree.analysis.{Frame, Interpreter}
import org.objectweb.asm.tree.{AbstractInsnNode, MethodNode}

object ParameterToResultFlow {
  /**
   * `flow(i) = true` means that it is possible that the method will return the passed i-th parameter (identity).
   * Symbolically, `foo(x, @Flow y, z)` means that in some circumstances `foo(.., y, ..) = y` may hold.
   * `flow(i) = false` means that it is impossible that `foo(.., y, ..) = y` holds.
   * The result of this analysis is used for deciding to infer or not to infer contract for this parameter (see faba.scala).
   * The starting point for this analysis is parameters from result origins analysis
   * (parameters that may flow into result without flowing through other methods)
   *
   * @param methodNode method bytecode
   * @param leaking leaking parameters
   * @param origins result origins
   * @return param influence
   */
  def analyze(methodNode: MethodNode, leaking: LeakingParameters, origins: Origins): Array[Boolean] = {
    val leakingParameters = origins.parameters
    val interpreter = new ParameterToResultInterpreter(java.util.Arrays.copyOf(leakingParameters, leakingParameters.length))
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
              // here parameter flowing into methods which may flow into a result are collected
              new Frame(frame).execute(insnNode, interpreter)
            case _ =>
          }
      }
      i += 1
    }
    interpreter.flow
  }
}

private class ParameterToResultInterpreter(val flow: Array[Boolean]) extends Interpreter[ParamsValue](ASM5) {
  val val1 = ParamsValue(Set(), 1)
  // we are interested only in passing parameters to methods flowing into result
  // this method is called from `ParameterToResultFlow#analyze` only for instructions at which
  // the result of method execution is born
  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: ParamsValue]): ParamsValue = {
    val opcode = insn.getOpcode
    opcode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL | INVOKEINTERFACE =>
        var n = if (opcode == INVOKESTATIC) 0 else 1
        while (n < values.size()) {
          for (i <- values.get(n).params)
            flow(i) = true
          n += 1
        }
      case _ =>
    }
    val1
  }

  // we don't need real implementation of following methods since they will not be called at all
  override def newValue(`type`: Type) = ???
  override def newOperation(insn: AbstractInsnNode) = ???
  override def binaryOperation(insn: AbstractInsnNode, value1: ParamsValue, value2: ParamsValue) = ???
  override def unaryOperation(insn: AbstractInsnNode, value: ParamsValue) = ???
  override def ternaryOperation(insn: AbstractInsnNode, value1: ParamsValue, value2: ParamsValue, value3: ParamsValue) = ???
  override def returnOperation(insn: AbstractInsnNode, value: ParamsValue, expected: ParamsValue) = ???
  override def copyOperation(insn: AbstractInsnNode, value: ParamsValue) = ???
  override def merge(v: ParamsValue, w: ParamsValue) = ???
}
