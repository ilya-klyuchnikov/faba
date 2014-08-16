package faba.asm

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.Type
import org.objectweb.asm.tree._
import org.objectweb.asm.tree.analysis.{Analyzer, Frame, Interpreter, Value}

import scala.collection.JavaConversions._

case class LeakingParameters(frames: Array[Frame[ParamsValue]],
                             parameters: Array[Boolean],
                             nullableParameters: Array[Boolean])

object LeakingParameters {
  def build(className: String, methodNode: MethodNode, jsr: Boolean): LeakingParameters = {
    val frames =
      if (jsr) new Analyzer(new ParametersUsage(methodNode)).analyze(className, methodNode)
      else new LiteAnalyzer(new ParametersUsage(methodNode)).analyze(className, methodNode)
    val insns = methodNode.instructions
    val collector = new LeakingParametersCollector(methodNode)
    val collector2 = new NullableLeakingParametersCollector(methodNode)
    for (i <- 0 until frames.length) {
      val insnNode = insns.get(i)
      val frame = frames(i)
      if (frame != null) insnNode.getType match {
        case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
        case _ =>
          new Frame(frame).execute(insnNode, collector)
          new Frame(frame).execute(insnNode, collector2)
      }
    }
    LeakingParameters(frames, collector.parameters, collector2.parameters)
  }
}

case class ParamsValue(params: Set[Int], size: Int) extends Value {
  override def getSize: Int = size
}

// tracks flow of parameters into values of frame
class ParametersUsage(m: MethodNode) extends Interpreter[ParamsValue](ASM5) {
  val val1 = ParamsValue(Set(), 1)
  val val2 = ParamsValue(Set(), 2)
  var called = -1
  // the first time newValue is called for return
  // the second time (if any) for `this`
  val shift = if ((m.access & ACC_STATIC) == 0) 2 else 1
  val range = shift until (Type.getArgumentTypes(m.desc).length + shift)

  override def newValue(tp: Type): ParamsValue = {
    if (tp == null)
      return val1
    called += 1
    // hack for analyzer
    if (range.contains(called)) {
      if (tp eq Type.VOID_TYPE) return null
      if (Utils.isReferenceType(tp) || Utils.isBooleanType(tp)) {
        if (tp.getSize == 1) ParamsValue(Set(called - shift), 1)
        else ParamsValue(Set(called - shift), 2)
      } else {
        // we are not interested in such parameters
        if (tp.getSize == 1) val1 else val2
      }
    } else {
      if (tp eq Type.VOID_TYPE) null
      else if (tp.getSize == 1) val1
      else val2
    }
  }


  override def newOperation(insn: AbstractInsnNode): ParamsValue =
    insn.getOpcode match {
      case LCONST_0 | LCONST_1 | DCONST_0 | DCONST_1 =>
        val2
      case LDC =>
        val cst = insn.asInstanceOf[LdcInsnNode].cst
        if (cst.isInstanceOf[Long] || cst.isInstanceOf[Double]) val2 else val1
      case GETSTATIC =>
        if (Utils.getSizeFast(insn.asInstanceOf[FieldInsnNode].desc) == 1) val1 else val2
      case _ =>
        val1
    }

  override def binaryOperation(insn: AbstractInsnNode, value1: ParamsValue, value2: ParamsValue): ParamsValue =
    insn.getOpcode match {
      case LALOAD | DALOAD | LADD | DADD | LSUB | DSUB | LMUL | DMUL |
           LDIV | DDIV | LREM | LSHL | LSHR | LUSHR | LAND | LOR | LXOR =>
        val2
      case _ =>
        val1
    }

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: ParamsValue]): ParamsValue =
    insn.getOpcode match {
      case MULTIANEWARRAY =>
        val1
      case INVOKEDYNAMIC =>
        if (Utils.getReturnSizeFast(insn.asInstanceOf[InvokeDynamicInsnNode].desc) == 1) val1 else val2
      case _ =>
        if (Utils.getReturnSizeFast(insn.asInstanceOf[MethodInsnNode].desc) == 1) val1 else val2
    }

  override def unaryOperation(insn: AbstractInsnNode, value: ParamsValue): ParamsValue =
    insn.getOpcode match {
      case LNEG | DNEG | I2L | I2D | L2D | F2L | F2D | D2L =>
        val2
      case GETFIELD =>
        if (Utils.getSizeFast(insn.asInstanceOf[FieldInsnNode].desc) == 1) val1 else val2
      case CHECKCAST =>
        ParamsValue(value.params, 1)
      case _ =>
        val1
    }

  override def ternaryOperation(insn: AbstractInsnNode, value1: ParamsValue, value2: ParamsValue, value3: ParamsValue): ParamsValue =
    val1

  override def returnOperation(insn: AbstractInsnNode, value: ParamsValue, expected: ParamsValue): Unit = ()

  override def copyOperation(insn: AbstractInsnNode, value: ParamsValue): ParamsValue =
    value

  override def merge(v: ParamsValue, w: ParamsValue): ParamsValue = (v, w) match {
    case (_, `v`) =>
      v
    case (ParamsValue(set1, size1), ParamsValue(set2, size2)) =>
      ParamsValue(set1 ++ set2, math.min(size1, size2))
    case _ =>
      v
  }
}

class LeakingParametersCollector(m: MethodNode) extends ParametersUsage(m) {
  val arity = Type.getArgumentTypes(m.desc).length
  val parameters = new Array[Boolean](arity)
  //val nullableParameters = new Array[Boolean](arity)

  override def unaryOperation(insn: AbstractInsnNode, v: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER | INSTANCEOF | IRETURN | ARETURN |
           IFNONNULL | IFNULL | IFEQ | IFNE =>
        for (i <- v.params) {
          parameters(i) = true
          //nullableParameters(i) = true
        }
      case _ =>
    }
    super.unaryOperation(insn, v)
  }

  override def binaryOperation(insn: AbstractInsnNode, v1: ParamsValue, v2: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case PUTFIELD =>
        for (i <- v1.params) {
          parameters(i) = true
          //nullableParameters(i) = true
        }
        for (i <- v2.params) {
          //nullableParameters(i) = true
        }
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD =>
        for (i <- v1.params) {
          parameters(i) = true
          //nullableParameters(i) = true
        }
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  override def ternaryOperation(insn: AbstractInsnNode, v1: ParamsValue, v2: ParamsValue, v3: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case AASTORE =>
        for (i <- v1.params) {
          parameters(i) = true
          //nullableParameters(i) = true
        }
        for (i <- v3.params) {
          //nullableParameters(i) = true
        }
      case IASTORE | LASTORE | FASTORE | DASTORE | BASTORE | CASTORE | SASTORE =>
        for (i <- v1.params) {
          parameters(i) = true
          //nullableParameters(i) = true
        }
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: ParamsValue]): ParamsValue = {
    insn.getOpcode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL | INVOKEINTERFACE =>
        for (v <- values; i <- v.params) {
          parameters(i) = true
          //nullableParameters(i) = true
        }
      case _ =>
    }
    super.naryOperation(insn, values)
  }

}

// special handling of passing param into field and into an array
class NullableLeakingParametersCollector(m: MethodNode) extends LeakingParametersCollector(m) {
  override def binaryOperation(insn: AbstractInsnNode, v1: ParamsValue, v2: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case PUTFIELD =>
        for (i <- v1.params) {
          parameters(i) = true
        }
        for (i <- v2.params) {
          parameters(i) = true
        }
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  override def ternaryOperation(insn: AbstractInsnNode, v1: ParamsValue, v2: ParamsValue, v3: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case AASTORE =>
        for (i <- v1.params) {
          parameters(i) = true
        }
        for (i <- v3.params) {
          parameters(i) = true
        }
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

}
