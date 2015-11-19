package faba.asm

import java.util

import faba.data._
import faba.data.{Key, Method}
import faba.engine._
import org.objectweb.asm.{Opcodes, Type}

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.analysis.{SourceValue, SourceInterpreter, Analyzer, Interpreter}
import org.objectweb.asm.tree._

import scala.annotation.switch
import scala.collection.JavaConverters._

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
  val finalTop = Final(Values.Top)
  val finalPure = Final(Values.Pure)

  val unAnalyzable = ACC_ABSTRACT | ACC_NATIVE | ACC_INTERFACE

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
        case (Values.ThisObject, Values.LocalEffect) =>
          Values.LocalEffect
        case (Values.LocalEffect, Values.ThisObject) =>
          Values.LocalEffect
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

    for (hardCodedSolution <- HardCodedPurity.getHardCodedSolution(aKey))
      return Equation(aKey, Final(hardCodedSolution))

    val instanceMethod = (methodNode.access & Opcodes.ACC_STATIC) == 0

    if ((methodNode.access & unAnalyzable) != 0)
      return Equation(aKey, finalTop)

    var calls: Set[Component[Key, Value]] = Set()
    val insns = methodNode.instructions

    val dataInterpreter = new DataInterpreter(methodNode)
    new Analyzer(dataInterpreter).analyze("this", methodNode)

    val ownershipInterpreter = new OwnershipInterpreter(methodNode)
    // hack to initialize this var
    new Analyzer(ownershipInterpreter).analyze("this", methodNode)
    val localInsns = ownershipInterpreter.localInsns
    val thisInsns = ownershipInterpreter.thisInsns

    for (i <- 0 until insns.size()) {
      val insn = insns.get(i)
      (insn.getOpcode: @switch) match {
        case PUTFIELD | IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE |
             INVOKEDYNAMIC | INVOKEINTERFACE =>
          if (thisInsns(insns.indexOf(insn))) {
            calls += Component(Values.LocalEffect, Set())
          }
          else if (!localInsns(insns.indexOf(insn)))
            return Equation(aKey, finalTop)
        case PUTSTATIC | INVOKEDYNAMIC | INVOKEINTERFACE =>
          return Equation(aKey, finalTop)
        case INVOKESTATIC =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          if (isArrayCopy(mNode) && localInsns(insns.indexOf(insn))) {
            // nothing
          }
          else {
            calls += Component(Values.NonLocalObject, Set(Key(Method(mNode.owner, mNode.name, mNode.desc), Out, stable = true)))
          }
        case INVOKEVIRTUAL | INVOKESPECIAL =>
          val locality =
            if (thisInsns(i)) Values.ThisObject
            else if (localInsns(i)) Values.LocalObject
            else Values.NonLocalObject
          val mNode = insn.asInstanceOf[MethodInsnNode]
          calls += Component(locality, Set(Key(Method(mNode.owner, mNode.name, mNode.desc), Out, stable = insn.getOpcode == INVOKESPECIAL)))
        case _ =>

      }
    }

    if (calls.isEmpty)
      Equation(aKey, finalPure)
    else
      Equation(aKey, Pending(calls))
  }

  def isArrayCopy(mnode: MethodInsnNode) =
    mnode.owner == "java/lang/System" && mnode.name == "arraycopy"

  case class ThisValue() extends SourceValue(1)

  class OwnershipInterpreter(m: MethodNode) extends SourceInterpreter {
    // all values except ones created in this method (new objects and new arrays) are unknown
    val unknownSourceVal1 = new SourceValue(1)
    val unknownSourceVal2 = new SourceValue(2)

    val insns = m.instructions

    // instructions that are executed over owned objects
    // owned objects are objects created inside this method and not passed into another methods
    val localInsns = new Array[Boolean](insns.size())
    val thisInsns = new Array[Boolean](insns.size())

    override def newValue(tp: Type): SourceValue =
      if (tp != null && tp.toString == "Lthis;") ThisValue() else super.newValue(tp)

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

    override def binaryOperation(insn: AbstractInsnNode, value1: SourceValue, value2: SourceValue) = {
      val index = insns.indexOf(insn)
      thisInsns(index) = false
      localInsns(index) = false
      insn.getOpcode match {
        case LALOAD | DALOAD | LADD | DADD | LSUB | DSUB | LMUL | DMUL |
             LDIV | DDIV | LREM | LSHL | LSHR | LUSHR | LAND | LOR | LXOR =>
          unknownSourceVal2
        case PUTFIELD =>
          // if field is put into `this` value, then instruction is this instruction
          thisInsns(index) = value1.isInstanceOf[ThisValue]
          // if field is put into owned value, then instruction is owned
          localInsns(index) = !value1.insns.isEmpty
          unknownSourceVal1
        case _ =>
          unknownSourceVal1
      }
    }


    final override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: SourceValue]): SourceValue = {
      val index = insns.indexOf(insn)
      thisInsns(index) = false
      localInsns(index) = false
      val opCode = insn.getOpcode
      opCode match {
        case MULTIANEWARRAY =>
          new SourceValue(1, insn)
        case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL =>
          val mNode = insn.asInstanceOf[MethodInsnNode]
          // arraycopy(src, srcPos, dest, destPos, length)
          if (isArrayCopy(mNode)) {
            localInsns(index) = !values.get(2).insns.isEmpty
          }
          if (opCode == INVOKESPECIAL || opCode == INVOKEVIRTUAL) {
            thisInsns(index) = values.get(0).isInstanceOf[ThisValue]
            localInsns(index) = !values.get(0).insns.isEmpty
          }
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
      val index = insns.indexOf(insn)
      thisInsns(index) = false
      localInsns(index) = false
      localInsns(index) = !value1.insns.isEmpty
      unknownSourceVal1
    }


    override def copyOperation(insn: AbstractInsnNode, value: SourceValue) =
      value

    override def merge(v1: SourceValue, v2: SourceValue): SourceValue =
      if (v1.isInstanceOf[ThisValue] && v2.isInstanceOf[ThisValue])
        v1
      else if (v1.insns.isEmpty || v2.insns.isEmpty)
        new SourceValue(math.min(v1.size, v2.size))
      else
        super.merge(v1, v2)
  }

  // how data are divided
  sealed trait DataValue extends org.objectweb.asm.tree.analysis.Value
  case object ThisDataValue extends DataValue {
    override def getSize: Int = 1
  }
  case object LocalDataValue extends DataValue {
    override def getSize: Int = 1
  }
  case class ParameterDataValue(i: Int) extends DataValue {
    override def getSize: Int = 1
  }
  case object OwnedDataValue extends DataValue {
    override def getSize: Int = 1
  }
  case object UnknownDataValue1 extends DataValue {
    override def getSize: Int = 1
  }
  case object UnknownDataValue2 extends DataValue {
    override def getSize: Int = 2
  }

  // effects
  sealed trait EffectQuantum
  case object TopEffectQuantum extends EffectQuantum
  case object ThisChangeQuantum extends EffectQuantum
  case class ParamChangeQuantum(i: Int) extends EffectQuantum
  case class CallQuantum(key: Key, data: List[DataValue]) extends EffectQuantum

  class DataInterpreter(m: MethodNode) extends Interpreter[DataValue](ASM5) {
    var called = -1
    // the first time newValue is called for return
    // the second time (if any) for `this`
    val shift = if ((m.access & ACC_STATIC) == 0) 2 else 1
    val range = shift until (Type.getArgumentTypes(m.desc).length + shift)
    val effects: Array[EffectQuantum] = new Array[EffectQuantum](m.instructions.size())

    override def newValue(tp: Type): DataValue = {
      if (tp == null)
        return UnknownDataValue1
      called += 1
      // hack for analyzer
      if (tp != null && tp.toString == "Lthis;")
        ThisDataValue
      else if (range.contains(called)) {
        if (tp eq Type.VOID_TYPE) return null
        if (Utils.isReferenceType(tp)) {
          ParameterDataValue(called - shift)
        } else {
          // we are not interested in such parameters
          if (tp.getSize == 1) UnknownDataValue1 else UnknownDataValue2
        }
      } else {
        if (tp eq Type.VOID_TYPE) null
        else if (tp.getSize == 1) UnknownDataValue1
        else UnknownDataValue1
      }
    }

    override def newOperation(insn: AbstractInsnNode): DataValue =
      insn.getOpcode match {
        case NEW =>
          LocalDataValue
        case LCONST_0 | LCONST_1 | DCONST_0 | DCONST_1 =>
          UnknownDataValue2
        case LDC =>
          val cst = insn.asInstanceOf[LdcInsnNode].cst
          val size = if (cst.isInstanceOf[Long] || cst.isInstanceOf[Double]) 2 else 1
          if (size == 1) UnknownDataValue1 else UnknownDataValue2
        case GETSTATIC =>
          val size = Type.getType(insn.asInstanceOf[FieldInsnNode].desc).getSize
          if (size == 1) UnknownDataValue1 else UnknownDataValue2
        case _ =>
          UnknownDataValue1
      }

    override def binaryOperation(insn: AbstractInsnNode, value1: DataValue, value2: DataValue): DataValue =
      insn.getOpcode match {
        case LALOAD | DALOAD | LADD | DADD | LSUB | DSUB | LMUL | DMUL |
             LDIV | DDIV | LREM | LSHL | LSHR | LUSHR | LAND | LOR | LXOR =>
          UnknownDataValue2
        case PUTFIELD =>
          val effectQuantum: EffectQuantum = value1 match {
            case ThisDataValue =>
              ThisChangeQuantum
            case OwnedDataValue =>
              ThisChangeQuantum
            case LocalDataValue =>
              null
            case ParameterDataValue(n) =>
              ParamChangeQuantum(n)
            case UnknownDataValue1 | UnknownDataValue2 =>
              TopEffectQuantum
          }
          val insnIndex = m.instructions.indexOf(insn)
          effects(insnIndex) = effectQuantum
          UnknownDataValue1
        case _ =>
          UnknownDataValue1
      }

    override def copyOperation(insn: AbstractInsnNode, value: DataValue): DataValue =
      value

    override def naryOperation(insn: AbstractInsnNode, values: util.List[_ <: DataValue]): DataValue = {
      val insnIndex = m.instructions.indexOf(insn)
      val opCode = insn.getOpcode
      opCode match {
        case MULTIANEWARRAY =>
          LocalDataValue
        case INVOKEDYNAMIC =>
          effects(insnIndex) = TopEffectQuantum
          if (Utils.getReturnSizeFast(insn.asInstanceOf[InvokeDynamicInsnNode].desc) == 1)
            UnknownDataValue1
          else
            UnknownDataValue2
        case INVOKEVIRTUAL | INVOKESPECIAL | INVOKESTATIC | INVOKEINTERFACE =>
          val stable = opCode == INVOKESPECIAL || opCode == INVOKESTATIC
          val data: List[DataValue] = values.asScala.toList
          val mNode = insn.asInstanceOf[MethodInsnNode]
          val key = Key(Method(mNode.owner, mNode.name, mNode.desc), Out, stable)
          effects(insnIndex) = CallQuantum(key, data)
          if (Utils.getReturnSizeFast(insn.asInstanceOf[MethodInsnNode].desc) == 1)
            UnknownDataValue1
          else
            UnknownDataValue2
      }
    }

    override def unaryOperation(insn: AbstractInsnNode, value: DataValue): DataValue =
      insn.getOpcode match {
        case LNEG | DNEG | I2L | I2D | L2D | F2L | F2D | D2L =>
          UnknownDataValue2
        case GETFIELD =>
          val fieldInsn = insn.asInstanceOf[FieldInsnNode]
          if (value == ThisDataValue && HardCodedPurity.ownedFields((fieldInsn.owner, fieldInsn.name))) {
            OwnedDataValue
          }
          else if (Utils.getSizeFast(fieldInsn.desc) == 1) UnknownDataValue1 else UnknownDataValue2
        case CHECKCAST =>
          value
        case PUTSTATIC =>
          val insnIndex = m.instructions.indexOf(insn)
          effects(insnIndex) = TopEffectQuantum
          UnknownDataValue1
        case _ =>
          UnknownDataValue1
      }

    override def ternaryOperation(insn: AbstractInsnNode, value1: DataValue, value2: DataValue, value3: DataValue): DataValue = {
      val effect: EffectQuantum = value1 match {
        case ThisDataValue | OwnedDataValue =>
          ThisChangeQuantum
        case ParameterDataValue(n) =>
          ParamChangeQuantum(n)
        case LocalDataValue =>
          null
        case UnknownDataValue1 | UnknownDataValue2 =>
          TopEffectQuantum
      }
      val insnIndex = m.instructions.indexOf(insn)
      effects(insnIndex) = effect
      UnknownDataValue1
    }

    override def returnOperation(insn: AbstractInsnNode, value: DataValue, expected: DataValue): Unit =
      ()

    override def merge(v1: DataValue, v2: DataValue): DataValue =
      if (v1 == v2)
        v1
      else {
        val size = math.min(v1.getSize, v2.getSize)
        if (size == 1) UnknownDataValue1 else UnknownDataValue2
      }
  }
}

object HardCodedPurity {

  val ownedFields: Set[(String, String)] =
    Set()

  val solutions: Map[Key, Value] =
    Map(Key(Method("java/lang/Throwable", "fillInStackTrace", "(I)Ljava/lang/Throwable;"), Out, stable = true) -> Values.LocalEffect)

  def getHardCodedSolution(aKey: Key): Option[Value] = {
    aKey match {
      case Key(Method(_, "fillInStackTrace", "()Ljava/lang/Throwable;"), _, _, _) =>
        Some(Values.LocalEffect)
      case _ => solutions.get(aKey)
    }
  }
}

class PuritySolver(negator: Negator[Values.Value], doNothing: Boolean)(implicit lattice: Lattice[Values.Value]) extends Solver[Key, Values.Value](negator, doNothing)(lattice) {
  override def mkUnstableValue(k: Key, v: Values.Value): Values.Value =
    HardCodedPurity.getHardCodedSolution(k) match {
      case Some(u) =>
        u
      case _ =>
        super.mkUnstableValue(k, v)
    }
}
