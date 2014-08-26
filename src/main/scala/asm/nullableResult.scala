package faba.asm.nullableResult

import faba.analysis.NullValue
import faba.asm.{InterpreterExt, AnalyzerExt}
import faba.data._
import faba.engine._
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.analysis.{BasicInterpreter, BasicValue}
import org.objectweb.asm.tree._
import org.objectweb.asm.{Opcodes, Type}
case class Calls(keys: Set[Key]) extends BasicValue(NullableResultAnalysis.ObjectType)
case class ThisValue() extends BasicValue(NullableResultAnalysis.ObjectType)

object NullableResultAnalysis {
  val ObjectType = Type.getObjectType("java/lang/Object")
  def analyze(className: String, methodNode: MethodNode, origins: Array[Boolean]): Result[Key, Value] = {
    val insns = methodNode.instructions
    val data = new Array[Set[Key]](insns.size())
    val analyzer = new AnalyzerExt[BasicValue, Set[Key], NullableResultInterpreter](NullableResultInterpreter(insns, origins), data, Set())
    val frames = analyzer.analyze("this", methodNode)
    var result = BasicValue.REFERENCE_VALUE
    for (i <- 0 until frames.length) {
      val frame = frames(i)
      if (frame != null && insns.get(i).getOpcode == Opcodes.ARETURN) {
        val derefs = analyzer.getData()(i)
        result = combine(result, frame.pop(), derefs)
      }
    }
    mkEquation(result)
  }

  def combine(v1: BasicValue, v2: BasicValue, derefs: Set[Key]): BasicValue = (v1, v2) match {
    case (NullValue(), _) =>
      NullValue()
    case (_, NullValue()) =>
      NullValue()
    case (Calls(keys1), Calls(keys2)) =>
      Calls(keys1 ++ (keys2 -- derefs))
    case (Calls(_), _) =>
      v1
    case (_, Calls(keys)) =>
      Calls(keys -- derefs)
    case _ =>
      BasicValue.REFERENCE_VALUE
  }

  def mkEquation(v: BasicValue): Result[Key, Value] = v match {
    case NullValue() =>
      Final(Values.Null)
    case Calls(keys) =>
      Pending[Key, Value](keys map { k => Component(Values.Null, Set(k)) })
    case _ =>
      Final(Values.Bot)
  }
}

case class NullableResultInterpreter(insns: InsnList, origins: Array[Boolean]) extends BasicInterpreter with InterpreterExt[Set[Key]] {

  override def newValue(tp: Type): BasicValue =
    if (tp != null && tp.toString == "Lthis;") ThisValue() else super.newValue(tp)

  override def newOperation(insn: AbstractInsnNode): BasicValue =
    if (insn.getOpcode == Opcodes.ACONST_NULL)
      NullValue()
    else
      super.newOperation(insn)

  final override def unaryOperation(insn: AbstractInsnNode, value: BasicValue): BasicValue = {
    insn.getOpcode match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER if value.isInstanceOf[Calls] =>
        delta = value.asInstanceOf[Calls].keys
      case _ =>
    }
    super.unaryOperation(insn, value)
  }

  final override def binaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue): BasicValue = {
    insn.getOpcode match {
      case PUTFIELD | IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD if v1.isInstanceOf[Calls] =>
        delta = v1.asInstanceOf[Calls].keys
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  final override def ternaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue, v3: BasicValue): BasicValue = {
    insn.getOpcode match {
      case IASTORE | LASTORE | FASTORE | DASTORE | BASTORE | CASTORE | SASTORE | AASTORE =>
        if (v1.isInstanceOf[Calls])
          delta = v1.asInstanceOf[Calls].keys
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    opCode match {
      case INVOKESPECIAL | INVOKEINTERFACE | INVOKEVIRTUAL | INVOKEDYNAMIC =>
        // handling dereferencing
        values.get(0) match {
          case Calls(keys) =>
            delta = keys
          case _ =>
        }
      case _ =>
    }
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL =>
        val stable =
          if (opCode == INVOKESTATIC || opCode == INVOKESPECIAL) true
          else values.get(0).isInstanceOf[ThisValue]
        val mNode = insn.asInstanceOf[MethodInsnNode]
        val method = Method(mNode.owner, mNode.name, mNode.desc)
        val retType = Type.getReturnType(mNode.desc)
        val isRefRetType = retType.getSort == Type.OBJECT || retType.getSort == Type.ARRAY
        if (isRefRetType && origins(insns.indexOf(insn)))
          return Calls(Set(Key(method, Out, stable)))
      case _ =>
    }
    super.naryOperation(insn, values)
  }

  override def merge(v1: BasicValue, v2: BasicValue): BasicValue = (v1, v2) match {
    case (NullValue(), _) =>
      NullValue()
    case (_, NullValue()) =>
      NullValue()
    case (Calls(keys1), Calls(keys2)) =>
      Calls(keys1 ++ keys2)
    case (Calls(_), _) =>
      v1
    case (_, Calls(_)) =>
      v2
    case _ =>
      super.merge(v1, v2)
  }

  var dereferenced: Set[Key] = null
  var delta: Set[Key] = null

  override def init(previous: Set[Key]) {
    dereferenced = previous
    delta = Set()
  }

  override def getAfterData: Set[Key] =
    dereferenced ++ delta

  // all keys that were dereferenced to this point
  override def merge(data1: Set[Key], data2: Set[Key]): Set[Key] =
    data1 ++ data2
}
