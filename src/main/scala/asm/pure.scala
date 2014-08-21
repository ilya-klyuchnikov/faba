package faba.asm

import faba.data._
import faba.data.{Key, Method}
import faba.engine.{Component, Pending, Final, Equation}
import org.objectweb.asm.tree.{MethodInsnNode, MethodNode}
import org.objectweb.asm.Opcodes._

import scala.annotation.switch

/**
 * create equation for inference of @Pure annotation
 */
object PureAnalysis {
  val finalTop = new Final(Values.Top)
  val finalPure = new Final(Values.Pure)
  val unknown = ACC_ABSTRACT | ACC_NATIVE | ACC_INTERFACE

  def analyze(method: Method, methodNode: MethodNode, stable: Boolean): Equation[Key, Value] = {
    val aKey = new Key(method, Out, stable)

    if ((methodNode.access & unknown) != 0)
      return Equation(aKey, finalTop)

    var calls: Set[Key] = Set()
    val insns = methodNode.instructions

    for (i <- 0 until insns.size()) {
      val insn = insns.get(i)
      (insn.getOpcode: @switch) match {
        case PUTFIELD | PUTSTATIC |
             IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE |
             INVOKEDYNAMIC | INVOKEINTERFACE =>
          return Equation(aKey, finalTop)
        case INVOKESPECIAL | INVOKESTATIC =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          calls += Key(Method(mNode.owner, mNode.name, mNode.desc), Out, true)
        case INVOKEVIRTUAL =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          val method = Method(mNode.owner, mNode.name, mNode.desc)
          calls += Key(method, Out, false)
        case _ =>

      }
    }
    if (calls.isEmpty)
      Equation(aKey, finalPure)
    else
      Equation(aKey, Pending(calls.map(k => Component(Values.Top, Set(k)))))
  }
}
