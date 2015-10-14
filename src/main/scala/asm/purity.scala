package faba.asm

import faba.data._
import faba.data.{Key, Method}
import faba.engine.{Component, Pending, Final, Equation}
import org.objectweb.asm.Opcodes._

import org.objectweb.asm.Type
import org.objectweb.asm.tree.analysis.{SourceValue, SourceInterpreter, Analyzer}
import org.objectweb.asm.tree._


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
 * Although all writes are to owned objects (created inside this method).
 *
 * - Nested calls (via INVOKESPECIAL, INVOKESTATIC, INVOKEVIRTUAL) are processed by transitivity.
 */
object PurityAnalysis {
  val finalTop = new Final(Values.Top)
  val finalPure = new Final(Values.Pure)

  val unAnalyzable = ACC_ABSTRACT | ACC_NATIVE | ACC_INTERFACE

  def analyze(method: Method, methodNode: MethodNode, stable: Boolean): Equation[Key, Value] = {
    val aKey = new Key(method, Out, stable)

    if ((methodNode.access & unAnalyzable) != 0)
      return Equation(aKey, finalTop)

    var calls: Set[Key] = Set()
    val insns = methodNode.instructions

    val ownershipInterpreter = new OwnershipInterpreter(insns)
    new Analyzer(ownershipInterpreter).analyze(method.internalClassName, methodNode)
    val ownedInsns = ownershipInterpreter.ownedInsn

    for (i <- 0 until insns.size()) {
      val insn = insns.get(i)
      (insn.getOpcode: @switch) match {
        case PUTFIELD | IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE |
             INVOKEDYNAMIC | INVOKEINTERFACE =>
          if (!ownedInsns(insns.indexOf(insn)))
            return Equation(aKey, finalTop)
        case PUTSTATIC | INVOKEDYNAMIC | INVOKEINTERFACE =>
          return Equation(aKey, finalTop)
        case INVOKESPECIAL | INVOKESTATIC =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          calls += Key(Method(mNode.owner, mNode.name, mNode.desc), Out, stable = true)
        case INVOKEVIRTUAL =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          calls += Key(Method(mNode.owner, mNode.name, mNode.desc), Out, stable = false)
        case _ =>

      }
    }
    if (calls.isEmpty)
      Equation(aKey, finalPure)
    else
      Equation(aKey, Pending(calls.map(k => Component(Values.Top, Set(k)))))
  }

  class OwnershipInterpreter(val insns: InsnList) extends SourceInterpreter {
    // all values except ones created in this method (new objects and new arrays) are unknown
    val unknownSourceVal1 = new SourceValue(1)
    val unknownSourceVal2 = new SourceValue(2)

    // instructions that are executed over owned objects
    // owned objects are objects created inside this method and not passed into another methods
    val ownedInsn = new Array[Boolean](insns.size())

    override def newOperation(insn: AbstractInsnNode): SourceValue = {
      val result = super.newOperation(insn)
      insn.getOpcode match {
        case NEW =>
          result // SIC!
        case _ =>
          new SourceValue(result.size)
      }
    }

    override def unaryOperation(insn: AbstractInsnNode, value: SourceValue) = {
      val result = super.unaryOperation(insn, value)
      insn.getOpcode match {
        case CHECKCAST =>
          value
        case NEWARRAY | ANEWARRAY =>
          result
        case _ =>
          new SourceValue(result.size)
      }
    }

    override def binaryOperation(insn: AbstractInsnNode, value1: SourceValue, value2: SourceValue) =
      insn.getOpcode match {
        case LALOAD | DALOAD | LADD | DADD | LSUB | DSUB | LMUL | DMUL |
             LDIV | DDIV | LREM | LSHL | LSHR | LUSHR | LAND | LOR | LXOR =>
          unknownSourceVal2
        case PUTFIELD =>
          // if field is put into owned value, then instruction is owned
          ownedInsn(insns.indexOf(insn)) = !value1.insns.isEmpty
          unknownSourceVal1
        case _ =>
          unknownSourceVal1
      }


    final override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: SourceValue]): SourceValue = {
      val opCode = insn.getOpcode
      opCode match {
        case MULTIANEWARRAY =>
          new SourceValue(1, insn)
        case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          val retType = Type.getReturnType(mNode.desc)
          if (retType.getSort == Type.OBJECT || retType.getSort == Type.ARRAY)
            unknownSourceVal1
          else if (retType.getSize == 1)
            unknownSourceVal1
          else
            unknownSourceVal2
        case INVOKEINTERFACE =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          val retType = Type.getReturnType(mNode.desc)
          if (retType.getSize == 1) unknownSourceVal1 else unknownSourceVal2
        case _ =>
          val mNode = insn.asInstanceOf[InvokeDynamicInsnNode]
          val retType = Type.getReturnType(mNode.desc)
          if (retType.getSize == 1) unknownSourceVal1 else unknownSourceVal2
      }
    }

    // writing to an owned array is an owned instruction
    override def ternaryOperation(insn: AbstractInsnNode, value1: SourceValue, value2: SourceValue, value3: SourceValue) = {
      ownedInsn(insns.indexOf(insn)) = !value1.insns.isEmpty
      unknownSourceVal1
    }


    override def copyOperation(insn: AbstractInsnNode, value: SourceValue) =
      value

    // owned merge owned = owned, otherwise, not owned
    override def merge(d: SourceValue, w: SourceValue): SourceValue =
      if (d.insns.isEmpty || w.insns.isEmpty)
        new SourceValue(math.min(d.size, w.size))
      else
        super.merge(d, w)
  }

}
