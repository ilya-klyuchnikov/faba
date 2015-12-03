package faba.asm

import java.util

import faba.data._
import org.objectweb.asm.{Opcodes, Type}

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.analysis.{Analyzer, Interpreter}
import org.objectweb.asm.tree._

import scala.collection.JavaConverters._

object PurityAnalysis {

  val unAnalyzable = ACC_ABSTRACT | ACC_NATIVE | ACC_INTERFACE

  def analyze(method: Method, methodNode: MethodNode, stable: Boolean): PurityEquation = {
    val aKey = new Key(method, Out, stable)

    for (hardCodedSolution <- HardCodedPurity.getHardCodedSolution(aKey))
      return PurityEquation(aKey, hardCodedSolution)

    if ((methodNode.access & unAnalyzable) != 0)
      return PurityEquation(aKey, Set[EffectQuantum](TopEffectQuantum))

    val dataInterpreter = new DataInterpreter(methodNode)
    new Analyzer(dataInterpreter).analyze("this", methodNode)
    val quanta = dataInterpreter.effects
    var effects = Set[EffectQuantum]()
    for (quantum <- quanta if quantum != null) {
      if (quantum == TopEffectQuantum) {
        effects = Set(TopEffectQuantum)
        return PurityEquation(aKey, effects)
      }
      effects = effects + quantum
    }
    PurityEquation(aKey, effects)
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
  case class CallQuantum(key: Key, data: List[DataValue], isStatic: Boolean) extends EffectQuantum
  case class PurityEquation(key: Key, effects: Set[EffectQuantum])

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
      if (tp.toString == "Lthis;")
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
        else UnknownDataValue2
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
          effects(insnIndex) = CallQuantum(key, data, opCode == INVOKESTATIC)
          if (Utils.getReturnSizeFast(mNode.desc) == 1)
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
        case NEWARRAY | ANEWARRAY =>
          LocalDataValue
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

  import PurityAnalysis._

  val ownedFields: Set[(String, String)] =
    Set(("java/lang/AbstractStringBuilder", "value"))

  val solutions: Map[Method, Set[EffectQuantum]] =
    Map(
      Method("java/lang/Throwable", "fillInStackTrace", "(I)Ljava/lang/Throwable;") -> Set(ThisChangeQuantum),
      Method("java/lang/System", "arraycopy", "(Ljava/lang/Object;ILjava/lang/Object;II)V") -> Set(ParamChangeQuantum(2)),
      Method("java/lang/AbstractStringBuilder", "expandCapacity", "(I)V") -> Set(ThisChangeQuantum),
      Method("java/lang/StringBuilder", "expandCapacity", "(I)V") -> Set(ThisChangeQuantum),
      Method("java/lang/StringBuffer", "expandCapacity", "(I)V") -> Set(ThisChangeQuantum),
      Method("java/lang/StringIndexOutOfBoundsException", "<init>", "(I)V") -> Set(ThisChangeQuantum)
    )

  def getHardCodedSolution(aKey: Key): Option[Set[EffectQuantum]] = aKey match {
    case Key(Method(_, "fillInStackTrace", "()Ljava/lang/Throwable;"), _, _, _) =>
      Some(Set(ThisChangeQuantum))
    case _ =>
      solutions.get(aKey.method)
  }
}


class PuritySolver {
  import PurityAnalysis._
  import scala.collection.mutable

  private var solved : Map[Key, Set[EffectQuantum]] = Map()
  private val dependencies = mutable.HashMap[Key, Set[Key]]()
  private val moving = mutable.Queue[PurityEquation]()
  private val pending = mutable.HashMap[Key, Set[EffectQuantum]]()

  def addEquation(eq: PurityEquation): Unit = {
    val key = eq.key
    val effects = eq.effects
    var callKeys = Set[Key]()
    for (effect <- effects) {
      effect match {
        case CallQuantum(callKey, _, _) =>
          callKeys = callKeys + callKey
        case _ =>

      }
    }

    if (callKeys.isEmpty) {
      moving.enqueue(eq)
    } else {
      pending(key) = effects
      for (callKey <- callKeys) {
        dependencies(callKey) = dependencies.getOrElse(callKey, Set()) + key
      }
    }
  }

  def mkUnstableValue(key: Key, effects: Set[EffectQuantum]): Set[EffectQuantum] =
    HardCodedPurity.getHardCodedSolution(key) match {
      case Some(set) => set
      case None => Set(TopEffectQuantum)
    }

  def solve(): Map[Key, Set[EffectQuantum]] = {
    while (moving.nonEmpty) {
      val eq = moving.dequeue()
      val key = eq.key
      val effects = eq.effects
      solved = solved + (key -> effects)

      val toPropagate: List[(Key, Set[EffectQuantum])] =
        if (key.stable)
          List((key, effects), (key.mkUnstable, effects))
        else
          List((key.mkStable, effects), (key, mkUnstableValue(key, effects)))

      // pEffect mayBe pure!
      for {
        (pKey, pEffects) <- toPropagate
        dKeys <- dependencies.remove(pKey)
        dKey <- dKeys
        dEffects <- pending.remove(dKey)
      } {
        var callKeys = Set[Key]()
        var newEffects = Set[EffectQuantum]()
        var delta: Set[EffectQuantum] = null
        for (dEffect <- dEffects) dEffect match {
          case CallQuantum(`pKey`, data, isStatic) =>
            delta = substitute(isStatic, pEffects, data)
            newEffects = newEffects ++ delta
          case otherCall:CallQuantum =>
            callKeys = callKeys + otherCall.key
            newEffects = newEffects + otherCall
          case _ =>
            newEffects = newEffects + dEffect
        }

        if (delta == Set(TopEffectQuantum)) {
          moving.enqueue(PurityEquation(dKey, Set(TopEffectQuantum)))
          // TODO - cleanup dependencies?
        } else if (callKeys.isEmpty) {
          moving.enqueue(PurityEquation(dKey, newEffects))
        } else {
          pending(dKey) = newEffects
        }

      }
    }
    solved
  }

  def substitute(isStatic: Boolean, effects: Set[EffectQuantum], data: List[DataValue]): Set[EffectQuantum] =
    if (effects.isEmpty) {
      effects
    } else if (effects == Set(TopEffectQuantum)) {
      Set(TopEffectQuantum)
    } else {
      var newEffects = Set[EffectQuantum]()
      val shift = if (isStatic) 0 else 1
      for (effect <- effects) effect match {
        case ThisChangeQuantum =>
          data.head match {
            case ThisDataValue | OwnedDataValue =>
              newEffects = newEffects + ThisChangeQuantum
            case LocalDataValue =>
              // nothing - pure
            case ParameterDataValue(n) =>
              newEffects = newEffects + ParamChangeQuantum(n)
            case _ =>
              // top
              return Set(TopEffectQuantum)
          }

        case ParamChangeQuantum(i) =>
          data(i + shift) match {
            case ThisDataValue | OwnedDataValue =>
              newEffects = newEffects + ThisChangeQuantum
            case LocalDataValue =>
              // nothing - pure
            case ParameterDataValue(n) =>
              newEffects = newEffects + ParamChangeQuantum(n)
            case _ =>
              // top
              return Set(TopEffectQuantum)
          }
      }

      newEffects
    }


}