package faba.asm

import faba.data._
import faba.data.{Key, Method}
import faba.engine._
import org.objectweb.asm.{Opcodes, Type}
import org.objectweb.asm.tree.analysis.{SourceValue, SourceInterpreter, Analyzer}
import org.objectweb.asm.tree._
import org.objectweb.asm.Opcodes._

import scala.annotation.switch

object PurityAnalysis {
  val finalTop = new Final(Values.Top)
  val finalPure = new Final(Values.Pure)
  val unknown = ACC_ABSTRACT | ACC_NATIVE | ACC_INTERFACE

  // Pure < local < top
  val purityLattice = new Lattice[Values.Value] {
    override val top: Values.Value = Values.Top
    override val bot: Values.Value = Values.Pure

    override def join(x: Values.Value, y: Values.Value): Values.Value = {
      (x, y) match {
        case (`bot`, _) => y
        case (_, `bot`) => x
        case (`top`, _) => top
        case (_, `top`) => top
        case (Values.Pure, Values.LocalEffect) =>
          Values.LocalEffect
        case (Values.LocalEffect, Values.Pure) =>
          Values.LocalEffect
        case _ => if (equiv(x, y)) x else top
      }
    }

    // current hack: one of values is locality
    override def meet(x: Values.Value, y: Values.Value): Values.Value = {
      (x, y) match {
        case (`top`, _) => top
        case (_, `top`) => top
        case (`bot`, _) => bot
        case (_, `bot`) => bot
        case (Values.LocalObject, Values.LocalEffect) =>
          Values.Pure
        case (Values.LocalEffect, Values.LocalObject) =>
          Values.Pure
        case (Values.NonLocalObject, Values.LocalEffect) =>
          Values.Top
        case (Values.LocalEffect, Values.NonLocalObject) =>
          Values.Top
        case _ =>
          if (equiv(x, y)) x else bot
      }
    }
  }

  def analyze(method: Method, methodNode: MethodNode, stable: Boolean): Equation[Key, Value] = {
    val aKey = new Key(method, Out, stable)
    val instanceMethod = (methodNode.access & Opcodes.ACC_STATIC) == 0
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


    val ownershipInterpreter = new OwnershipInterpreter(insns, instanceMethod)
    new Analyzer(ownershipInterpreter).analyze("this", methodNode)
    val ownedInsns = ownershipInterpreter.ownedInsn
    val thisInsns = ownershipInterpreter.thisInsn

    var calls: Set[Component[Key, Value]] = Set()

    for (i <- 0 until insns.size()) {
      val insn = insns.get(i)
      (insn.getOpcode: @switch) match {
        case PUTFIELD | IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE =>
          // Write to a field/array is a local effect. Local effect is OK for owned objects.
          if (thisInsns(insns.indexOf(insn))) {
            calls += Component(Values.LocalEffect, Set())
          } else if (!ownedInsns(insns.indexOf(insn)))
            return Equation(aKey, finalTop)
        case PUTSTATIC | INVOKEDYNAMIC | INVOKEINTERFACE =>
          return Equation(aKey, finalTop)
        case INVOKESPECIAL =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          calls += Component(Values.NonLocalObject, Set(Key(Method(mNode.owner, mNode.name, mNode.desc), Out, true)))
        case INVOKESTATIC =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          if (isArrayCopy(mNode) && ownedInsns(insns.indexOf(insn))) {
            // nothing - safe to copy to owned object
          } else
            calls += Component(Values.NonLocalObject, Set(Key(Method(mNode.owner, mNode.name, mNode.desc), Out, true)))
        case INVOKEVIRTUAL =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          calls += Component(Values.NonLocalObject, Set(Key(Method(mNode.owner, mNode.name, mNode.desc), Out, false)))
        case _ =>

      }
    }

    if (calls.isEmpty) Equation(aKey, finalPure) else Equation(aKey, Pending(calls))
  }

  def isArrayCopy(mnode: MethodInsnNode) =
    mnode.owner == "java/lang/System" && mnode.name == "arraycopy"

  case class ThisValue() extends SourceValue(1)

  class OwnershipInterpreter(val insns: InsnList, val instanceMethod: Boolean) extends SourceInterpreter {
    val sourceVal1 = new SourceValue(1)
    val sourceVal2 = new SourceValue(2)
    // instructions that are executed over owned objects
    // owned objects are objects created inside this method and not passed into another methods
    val ownedInsn = new Array[Boolean](insns.size())
    val thisInsn = new Array[Boolean](insns.size())

    override def newValue(tp: Type): SourceValue =
      if (tp != null && tp.toString == "Lthis;") ThisValue() else super.newValue(tp)

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
          thisInsn(insns.indexOf(insn)) = value1.isInstanceOf[ThisValue]
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
    override def merge(v1: SourceValue, v2: SourceValue): SourceValue =
      if (v1.isInstanceOf[ThisValue] && v2.isInstanceOf[ThisValue])
        v1
      else if (v1.insns.isEmpty || v2.insns.isEmpty)
        new SourceValue(math.min(v1.size, v2.size))
      else
        super.merge(v1, v2)
  }
}
