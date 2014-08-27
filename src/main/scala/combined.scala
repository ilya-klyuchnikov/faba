package faba.combined

import faba.analysis._
import faba.cfg.ControlFlowGraph
import faba.data._
import faba.engine._
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree._
import org.objectweb.asm.{Handle, Opcodes, Type}
import org.objectweb.asm.tree.analysis.{BasicInterpreter, BasicValue, Frame}

import scala.annotation.switch
import scala.collection.JavaConversions._

case class CallValue(tp: Type, method: Method, stableCall: Boolean, args: List[_ <: BasicValue]) extends BasicValue(tp)
case class NthParamValue(tp: Type, n: Int) extends BasicValue(tp)

// specialized class for analyzing methods without branching
// this is a good tutorial example
class CombinedSingleAnalysis(val method: Method, val controlFlow: ControlFlowGraph) {

  val methodNode = controlFlow.methodNode
  val interpreter = CombinedInterpreter(Type.getArgumentTypes(methodNode.desc).length)
  var returnValue: BasicValue = null
  var exception: Boolean = false

  final def analyze() {
    val frame = createStartFrame()
    var insnIndex = 0

    while (true) {
      val insnNode = methodNode.instructions.get(insnIndex)
      insnNode.getType match {
        case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
          insnIndex = controlFlow.transitions(insnIndex).head
        case _ =>
          insnNode.getOpcode match {
            case ATHROW =>
              exception = true
              return
            case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN =>
              returnValue = frame.pop()
              return
            case RETURN =>
              // nothing to return
              return
            case _ =>
              frame.execute(insnNode, interpreter)
              insnIndex = controlFlow.transitions(insnIndex).head
          }
      }
    }
  }

  def notNullParamEquation(i: Int, stable: Boolean): Equation[Key, Value] = {
    val key = Key(method, In(i), stable)
    val result: Result[Key, Value] =
      if (interpreter.dereferencedParams(i)) Final(Values.NotNull)
      else {
        val used = interpreter.parameterFlow.getOrElse(i, Set())
        if (used.isEmpty)
          Final(Values.Top)
        else
          Pending[Key, Value](Set(Component(Values.Top, used)))
      }
    Equation(key, result)
  }

  def nullableParamEquation(i: Int, stable: Boolean): Equation[Key, Value] = {
    val key = Key(method, In(i), stable)
    val result: Result[Key, Value] =
      if (interpreter.dereferencedParams(i) || interpreter.notNullableParams(i)) Final(Values.Top)
      else {
        returnValue match {
          case NthParamValue(_, `i`) =>
            Final(Values.Top)
          case _ =>
            val calls: Set[Key] = interpreter.parameterFlow.getOrElse(i, Set())
            if (calls.isEmpty)
              Final(Values.Null)
            else
              Pending[Key, Value](calls.map(k => Component(Values.Top, Set(k))))
        }

      }
    Equation(key, result)
  }

  def contractEquation(paramIndex: Int, inValue: Value, stable: Boolean): Equation[Key, Value] = {
    val key = Key(method, InOut(paramIndex, inValue), stable)
    val result: Result[Key, Value] =
      if (exception || (inValue == Values.Null && interpreter.dereferencedParams(paramIndex)))
        Final(Values.Bot)
      else {
        returnValue match {
          case FalseValue() =>
            Final(Values.False)
          case TrueValue() =>
            Final(Values.True)
          case NullValue() =>
            Final(Values.Null)
          case NotNullValue(_) =>
            Final(Values.NotNull)
          case NthParamValue(_, `paramIndex`) =>
            Final(inValue)
          case CallValue(retType, m, stableCall, args) =>
            val isRefRetType = retType.getSort == Type.OBJECT || retType.getSort == Type.ARRAY
            var keys = Set[Key]()
            for ((NthParamValue(_, `paramIndex`), j) <- args.zipWithIndex) {
              keys += Key(m, InOut(j, inValue), stableCall)
            }
            if (isRefRetType) {
              keys += Key(m, Out, stableCall)
            }
            if (keys.nonEmpty)
              Pending[Key, Value](Set(Component(Values.Top, keys)))
            else
              Final(Values.Top)
          case _ =>
            Final(Values.Top)
        }
      }
    Equation(key, result)
  }

  def outContractEquation(stable: Boolean): Equation[Key, Value] = {
    val key = Key(method, Out, stable)
    val result: Result[Key, Value] =
      if (exception) Final(Values.Bot)
      else {
        returnValue match {
          case FalseValue() =>
            Final(Values.False)
          case TrueValue() =>
            Final(Values.True)
          case NullValue() =>
            Final(Values.Null)
          case NotNullValue(_) =>
            Final(Values.NotNull)
          case CallValue(_, m, stableCall, args) =>
            val callKey = Key(m, Out, stableCall)
            Pending[Key, Value](Set(Component(Values.Top, Set(callKey))))
          case _ =>
            Final(Values.Top)
        }
      }
    Equation(key, result)
  }

  final def createStartFrame(): Frame[BasicValue] = {
    val frame = new Frame[BasicValue](methodNode.maxLocals, methodNode.maxStack)
    val returnType = Type.getReturnType(methodNode.desc)
    val returnValue = if (returnType == Type.VOID_TYPE) null else new BasicValue(returnType)
    frame.setReturn(returnValue)

    val args = Type.getArgumentTypes(methodNode.desc)
    var local = 0
    if ((methodNode.access & Opcodes.ACC_STATIC) == 0) {
      val basicValue = new NotNullValue(Type.getObjectType(controlFlow.className))
      frame.setLocal(local, basicValue)
      local += 1
    }
    for (i <- 0 until args.size) {
      val value = new NthParamValue(args(i), i)
      frame.setLocal(local, value)
      local += 1
      if (args(i).getSize == 2) {
        frame.setLocal(local, BasicValue.UNINITIALIZED_VALUE)
        local += 1
      }
    }
    while (local < methodNode.maxLocals) {
      frame.setLocal(local, BasicValue.UNINITIALIZED_VALUE)
      local += 1
    }
    frame
  }
}

// Full single-pass interpreter, propagates everything needed for analysis.
case class CombinedInterpreter(arity: Int) extends BasicInterpreter {
  // Parameters dereferenced during execution of a method, tracked by parameter's indices.
  // Dereferenced parameters are @NotNull.
  val dereferencedParams = new Array[Boolean](arity)

  // Parameters, that are written to something or passed to an interface methods.
  // This parameters cannot be @Nullable.
  var notNullableParams = new Array[Boolean](arity)

  // parameterFlow(i) for i-th parameter stores a set parameter positions it is passed to
  // parameter is @NotNull if any of its usages are @NotNull
  var parameterFlow = Map[Int, Set[Key]]()

  override def newOperation(insn: AbstractInsnNode): BasicValue = {
    (insn.getOpcode: @switch) match {
      case ICONST_0 =>
        FalseValue()
      case ICONST_1 =>
        TrueValue()
      case ACONST_NULL =>
        NullValue()
      case LDC =>
        insn.asInstanceOf[LdcInsnNode].cst match {
          case tp: Type if tp.getSort == Type.OBJECT || tp.getSort == Type.ARRAY =>
            NotNullValue(Type.getObjectType("java/lang/Class"))
          case tp: Type if tp.getSort == Type.METHOD =>
            NotNullValue(Type.getObjectType("java/lang/invoke/MethodType"))
          case s: String =>
            NotNullValue(Type.getObjectType("java/lang/String"))
          case h: Handle =>
            NotNullValue(Type.getObjectType("java/lang/invoke/MethodHandle"))
          case _ =>
            super.newOperation(insn)
        }
      case NEW =>
        NotNullValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc))
      case _ =>
        super.newOperation(insn)
    }
  }

  override def unaryOperation(insn: AbstractInsnNode, value: BasicValue): BasicValue = {
    (insn.getOpcode: @switch) match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER =>
        if (value.isInstanceOf[NthParamValue])
          dereferencedParams(value.asInstanceOf[NthParamValue].n) = true
        super.unaryOperation(insn, value)
      case CHECKCAST if value.isInstanceOf[NthParamValue] =>
        val nParam = value.asInstanceOf[NthParamValue]
        NthParamValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc), nParam.n)
      case NEWARRAY | ANEWARRAY =>
        NotNullValue(super.unaryOperation(insn, value).getType)
      case _ =>
        super.unaryOperation(insn, value)
    }
  }

  override def binaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue): BasicValue = {
    (insn.getOpcode: @switch) match {
      case PUTFIELD =>
        if (v1.isInstanceOf[NthParamValue])
          dereferencedParams(v1.asInstanceOf[NthParamValue].n) = true
        if (v2.isInstanceOf[NthParamValue])
          notNullableParams(v2.asInstanceOf[NthParamValue].n) = true
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD =>
        if (v1.isInstanceOf[NthParamValue])
          dereferencedParams(v1.asInstanceOf[NthParamValue].n) = true
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  @switch
  override def ternaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue, v3: BasicValue): BasicValue = {
    (insn.getOpcode: @switch) match {
      case IASTORE | LASTORE | FASTORE | DASTORE | BASTORE | CASTORE | SASTORE =>
        if (v1.isInstanceOf[NthParamValue])
          dereferencedParams(v1.asInstanceOf[NthParamValue].n) = true
      case AASTORE =>
        if (v1.isInstanceOf[NthParamValue])
          dereferencedParams(v1.asInstanceOf[NthParamValue].n) = true
        if (v3.isInstanceOf[NthParamValue])
          notNullableParams(v3.asInstanceOf[NthParamValue].n) = true
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val opCode = insn.getOpcode
    val shift = if (opCode == INVOKESTATIC) 0 else 1
    // catching explicit dereferences
    if (opCode == INVOKESPECIAL || opCode == INVOKEINTERFACE || opCode == INVOKEVIRTUAL) {
      values.get(0) match {
        case np: NthParamValue =>
          dereferencedParams(np.n) = true
        case _ =>
      }
    }
    (opCode: @switch) match {
      // catching implicit dereferences
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL | INVOKEINTERFACE =>
        val stable = opCode == INVOKESTATIC || opCode == INVOKESPECIAL
        val mNode = insn.asInstanceOf[MethodInsnNode]
        val retType = Type.getReturnType(mNode.desc)
        val method = Method(mNode.owner, mNode.name, mNode.desc)
        for (i <- shift until values.size()) {
          values.get(i) match {
            case np: NthParamValue =>
              if (opCode == INVOKEINTERFACE) {
                // no knowledge about interface
                notNullableParams(np.n) = true
              }
              else {
                val npKeys = parameterFlow.getOrElse(np.n, Set())
                val key = Key(method, In(i - shift), stable)
                parameterFlow = parameterFlow.updated(np.n, npKeys + key)
              }
            case _ =>
          }
        }
        CallValue(retType, method, stable, values.drop(shift).toList)
      case MULTIANEWARRAY =>
        NotNullValue(super.naryOperation(insn, values).getType)
      case _ =>
        super.naryOperation(insn, values)
    }

  }
}
