package faba.analysis.leakingParameters

import faba.analysis._

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.Type
import org.objectweb.asm.tree._
import org.objectweb.asm.tree.analysis.{Analyzer, Frame, Interpreter, Value}

import scala.collection.JavaConversions._

/**
 * Approximation of parameters usage.
 *
 * `parameter(i) = true` means that the result of method execution depends on a given parameter
 * in the following sense:
 * - parameter may be dereferences (thus, passing null to this parameter may produce NPE)
 * - parameter may be returned from the method
 * - branching in the method depends on this parameter
 *
 * if parameter(i) = false, then `@NotNull` parameter analysis for this parameter will produce no positive result.
 * if parameter(i) = false, then ResultAnalysis depending on this parameter will produce the same result as
 * ResultAnalysis for the whole method.
 *
 * if nullableParameters(i) = false, then passing `null` to this parameter is OK (will be no NPE)
 * if nullableParameters(i) = true, then it is worth to perform `@Nullable` result analysis
 *
 * @param frames fixed point of frames
 * @param parameters `parameter(i) = true` means that it is worth to perform `@NotNull` parameter analysis
 *                   and "null|!null->?" `@Contract` analysis.
 *                   `parameter(i) = false` means that `@NotNull` parameter analysis will not infer `@NotNull` for given parameter
 * @param nullableParameters `nullableParameter(i) = true` means that is worth to perform `@Nullable` parameter analysis
 *                           `nullableParameter(i) = false` means that `@Nullable` it is OK to pass `null` to this parameter
 * @param splittingParameters `splittingParameter(i) = true` means that there is branching performed on this parameter
 */
case class LeakingParameters(frames: Array[Frame[ParamsValue]],
                             parameters: Array[Boolean],
                             nullableParameters: Array[Boolean],
                             splittingParameters: Array[Boolean])

object LeakingParameters {
  def build(className: String, methodNode: MethodNode, jsr: Boolean): LeakingParameters = {
    val frames =
      if (jsr) new Analyzer(new ParametersUsageInterpreter(methodNode)).analyze(className, methodNode)
      else new LiteAnalyzer(new ParametersUsageInterpreter(methodNode)).analyze(className, methodNode)
    val insns = methodNode.instructions
    val collector = new LeakingParametersCollector(methodNode)
    for (i <- 0 until frames.length) {
      val insnNode = insns.get(i)
      val frame = frames(i)
      if (frame != null) insnNode.getType match {
        case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
        case _ =>
          new Frame(frame).execute(insnNode, collector)
      }
    }
    LeakingParameters(frames, collector.parameters, collector.nullableParameters, collector.splittingParameters)
  }
}

@AsmAbstractValue case class ParamsValue(params: Set[Int], size: Int) extends Value {
  override def getSize: Int = size
}

/**
 * For all positions (instruction + slot in a frame) calculates the super-set
 * of all possible parameters coming into this place (value = ParamsValue)
 * @param m bytecode of the method
 */
class ParametersUsageInterpreter(m: MethodNode) extends Interpreter[ParamsValue](ASM5) {
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
      if (AsmUtils.isReferenceType(tp)) {
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
        if (AsmUtils.getSizeFast(insn.asInstanceOf[FieldInsnNode].desc) == 1) val1 else val2
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
        if (AsmUtils.getReturnSizeFast(insn.asInstanceOf[InvokeDynamicInsnNode].desc) == 1) val1 else val2
      case _ =>
        if (AsmUtils.getReturnSizeFast(insn.asInstanceOf[MethodInsnNode].desc) == 1) val1 else val2
    }

  override def unaryOperation(insn: AbstractInsnNode, value: ParamsValue): ParamsValue =
    insn.getOpcode match {
      case LNEG | DNEG | I2L | I2D | L2D | F2L | F2D | D2L =>
        val2
      case GETFIELD =>
        if (AsmUtils.getSizeFast(insn.asInstanceOf[FieldInsnNode].desc) == 1) val1 else val2
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

/**
 * This collector (re-)executes instructions over fixpoint of ParamsValue
 * and populates `parameters`, `nullableParameters` and `splittingParameters`
 * @param m bytecode of the method
 */
class LeakingParametersCollector(m: MethodNode) extends ParametersUsageInterpreter(m) {
  val arity = Type.getArgumentTypes(m.desc).length
  val parameters = new Array[Boolean](arity)
  val nullableParameters = new Array[Boolean](arity)
  val splittingParameters = new Array[Boolean](arity)

  override def unaryOperation(insn: AbstractInsnNode, v: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case INSTANCEOF | IFNONNULL | IFNULL | IFEQ | IFNE =>
        for (i <- v.params) {
          parameters(i) = true
          nullableParameters(i) = true
          splittingParameters(i) = true
        }
      case GETFIELD | ARRAYLENGTH | MONITORENTER | IRETURN | ARETURN =>
        for (i <- v.params) {
          parameters(i) = true
          nullableParameters(i) = true
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
          nullableParameters(i) = true
        }
        for (i <- v2.params) {
          nullableParameters(i) = true
        }
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD =>
        for (i <- v1.params) {
          parameters(i) = true
          nullableParameters(i) = true
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
          nullableParameters(i) = true
        }
        for (i <- v3.params) {
          nullableParameters(i) = true
        }
      case IASTORE | LASTORE | FASTORE | DASTORE | BASTORE | CASTORE | SASTORE =>
        for (i <- v1.params) {
          parameters(i) = true
          nullableParameters(i) = true
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
          nullableParameters(i) = true
        }
      case _ =>
    }
    super.naryOperation(insn, values)
  }

}
