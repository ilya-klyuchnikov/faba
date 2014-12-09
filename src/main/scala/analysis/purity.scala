package faba.analysis.purity

import faba.calls.CallUtils
import faba.data._
import faba.engine._

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.{MethodInsnNode, MethodNode}

import scala.annotation.switch

/**
 * Produces equations for inference of @Contract(pure=true) annotations.
 *
 * This simple analysis infers @Contract(pure=true) only if the method doesn't have following instructions.
 * <ul>
 * <li>PUTFIELD</li>
 * <li>PUTSTATIC</li>
 * <li>IASTORE</li>
 * <li>LASTORE</li>
 * <li>FASTORE</li>
 * <li>DASTORE</li>
 * <li>AASTORE</li>
 * <li>BASTORE</li>
 * <li>CASTORE</li>
 * <li>SASTORE</li>
 * <li>INVOKEDYNAMIC</li>
 * <li>INVOKEINTERFACE</li>
 * </ul>
 *
 * - Nested calls (via INVOKESPECIAL, INVOKESTATIC, INVOKEVIRTUAL) are processed by transitivity.
 */
object PurityAnalysis {
  val finalTop = new Final(Values.Top)
  val finalPure = new Final(Values.Pure)

  val unAnalyzable = ACC_ABSTRACT | ACC_NATIVE | ACC_INTERFACE

  def analyze(method: Method, methodNode: MethodNode): Equation[Key, Value] = {
    val aKey = new Key(method, Out, ResolveDirection.Upward)

    if ((methodNode.access & unAnalyzable) != 0)
      return Equation(aKey, finalTop)

    var calls: Set[Key] = Set()
    val insns = methodNode.instructions

    for (i <- 0 until insns.size()) {
      val insn = insns.get(i)
      val opCode = insn.getOpcode
      (opCode: @switch) match {
        // TODO - INVOKEINTERFACE - later
        case PUTFIELD | PUTSTATIC |
             IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE |
             INVOKEDYNAMIC | INVOKEINTERFACE =>
          return Equation(aKey, finalTop)
        case INVOKESPECIAL | INVOKESTATIC | INVOKEVIRTUAL =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          calls += Key(Method(mNode.owner, mNode.name, mNode.desc), Out, CallUtils.callResolveDirection(opCode))
        case _ =>

      }
    }
    if (calls.isEmpty)
      Equation(aKey, finalPure)
    else
      Equation(aKey, Pending(calls.map(k => Product(Values.Top, Set(k)))))
  }
}
