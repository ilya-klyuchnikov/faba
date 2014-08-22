package faba.asm

import faba.data._
import faba.data.{Key, Method}
import faba.engine.{Component, Pending, Final, Equation}
import org.objectweb.asm.Type
import org.objectweb.asm.tree.analysis.{SourceValue, SourceInterpreter, Analyzer}
import org.objectweb.asm.tree._
import org.objectweb.asm.Opcodes._

import scala.annotation.switch

object PurityAnalysis {
  val finalTop = new Final(Values.Top)
  val finalPure = new Final(Values.Pure)
  val unknown = ACC_ABSTRACT | ACC_NATIVE | ACC_INTERFACE

  def analyze(method: Method, methodNode: MethodNode, stable: Boolean): Equation[Key, Value] = {
    val aKey = new Key(method, Out, stable)

    if ((methodNode.access & unknown) != 0)
      return Equation(aKey, finalTop)
    val insns = methodNode.instructions

    // the first pass - finding top ASAP
    for (i <- 0 until insns.size()) {
      val insn = insns.get(i)
      (insn.getOpcode: @switch) match {
        case PUTSTATIC | INVOKEDYNAMIC | INVOKEINTERFACE =>
          return Equation(aKey, finalTop)
        case _ =>
      }
    }


    val ownershipInterpreter = new OwnershipInterpreter(insns)
    new Analyzer(ownershipInterpreter).analyze(method.internalClassName, methodNode)
    val ownedInsns = ownershipInterpreter.ownedInsn

    var calls: Set[Key] = Set()

    for (i <- 0 until insns.size()) {
      val insn = insns.get(i)
      (insn.getOpcode: @switch) match {
        case PUTFIELD | IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE =>
          // Write to a field/array is a local effect. Local effect is OK for owned objects.
          if (!ownedInsns(insns.indexOf(insn)))
            return Equation(aKey, finalTop)
        case PUTSTATIC | INVOKEDYNAMIC | INVOKEINTERFACE =>
          return Equation(aKey, finalTop)
        case INVOKESPECIAL =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          calls += Key(Method(mNode.owner, mNode.name, mNode.desc), Out, true)
        case INVOKESTATIC =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          if (isArrayCopy(mNode) && ownedInsns(insns.indexOf(insn))) {
            // nothing - safe to copy to owned object
          } else
            calls += Key(Method(mNode.owner, mNode.name, mNode.desc), Out, true)
        case INVOKEVIRTUAL =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          calls += Key(Method(mNode.owner, mNode.name, mNode.desc), Out, false)
        case _ =>

      }
    }
    if (calls.isEmpty)
      Equation(aKey, finalPure)
    else
      Equation(aKey, Pending(calls.map(k => Component(Values.Top, Set(k)))))
  }

  def isArrayCopy(mnode: MethodInsnNode) =
    mnode.owner == "java/lang/System" && mnode.name == "arraycopy"

  class OwnershipInterpreter(val insns: InsnList) extends SourceInterpreter {
    val sourceVal1 = new SourceValue(1)
    val sourceVal2 = new SourceValue(2)
    // instructions that are executed over owned objects
    // owned objects are objects created inside this method and not passed into another methods
    val ownedInsn = new Array[Boolean](insns.size())

    override def newOperation(insn: AbstractInsnNode): SourceValue = {
      val result = super.newOperation(insn)
      insn.getOpcode match {
        case NEW =>
          result
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
          sourceVal2
        case PUTFIELD =>
          // if field is put into owned value, then instruction is owned
          ownedInsn(insns.indexOf(insn)) = !value1.insns.isEmpty
          sourceVal1
        case _ =>
          sourceVal1
      }


    final override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: SourceValue]): SourceValue = {
      val opCode = insn.getOpcode
      opCode match {
        case MULTIANEWARRAY =>
          new SourceValue(1, insn)
        case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          if (isArrayCopy(mNode)) {
            ownedInsn(insns.indexOf(insn)) = !values.get(2).insns.isEmpty
          }
          val retType = Type.getReturnType(mNode.desc)
          if (retType.getSort == Type.OBJECT || retType.getSort == Type.ARRAY)
            new SourceValue(1)
          else if (retType.getSize == 1)
            sourceVal1
          else
            sourceVal2
        case INVOKEINTERFACE =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          val retType = Type.getReturnType(mNode.desc)
          if (retType.getSize == 1) sourceVal1 else sourceVal2
        case _ =>
          val mNode = insn.asInstanceOf[InvokeDynamicInsnNode]
          val retType = Type.getReturnType(mNode.desc)
          if (retType.getSize == 1) sourceVal1 else sourceVal2
      }
    }

    override def ternaryOperation(insn: AbstractInsnNode, value1: SourceValue, value2: SourceValue, value3: SourceValue) = {
      ownedInsn(insns.indexOf(insn)) = !value1.insns.isEmpty
      sourceVal1
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
