package faba.analysis.combined

import faba.analysis._
import faba.calls.CallUtils
import faba.data._
import faba.engine._

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree._
import org.objectweb.asm.{Handle, Opcodes, Type}
import org.objectweb.asm.tree.analysis.{BasicInterpreter, BasicValue, Frame}

import scala.annotation.switch
import scala.collection.JavaConversions._

// a value that was created at an instruction with `origin` index
// origin is used as identity
trait Trackable {
  val origin: Int
}
@AsmAbstractValue case class TrackableCallValue(origin: Int, tp: Type, method: Method, resolveDirection: ResolveDirection.Value, args: List[_ <: BasicValue], callToThis: Boolean) extends BasicValue(tp) with Trackable
@AsmAbstractValue case class NthParamValue(tp: Type, n: Int) extends BasicValue(tp)
@AsmAbstractValue case class TrackableNullValue(origin: Int) extends BasicValue(Type.getObjectType("null")) with Trackable
@AsmAbstractValue case class TrackableValue(origin: Int, tp: Type) extends BasicValue(tp) with Trackable
@AsmAbstractValue case class ThisValue() extends BasicValue(Type.getObjectType("java/lang/Object"))

// specialized class for analyzing methods without branching
// this is a good tutorial example
class CombinedSingleAnalysis(val context: LiteContext) {
  import context._

  val interpreter = new CombinedInterpreter(methodNode.instructions, Type.getArgumentTypes(methodNode.desc).length)
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

  def notNullParamEquation(i: Int): Equation[Key, Value] = {
    val key = Key(method, In(i), resolveDirection)
    val result: Result[Key, Value] =
      if (interpreter.dereferencedParams(i)) Final(Values.NotNull)
      else {
        val used = interpreter.parameterFlow.getOrElse(i, Set())
        if (used.isEmpty)
          Final(Values.Top)
        else
          Pending[Key, Value](Set(Product(Values.Top, used)))
      }
    Equation(key, result)
  }

  def nullableParamEquation(i: Int): Equation[Key, Value] = {
    val key = Key(method, In(i), resolveDirection)
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
              Pending[Key, Value](calls.map(k => Product(Values.Top, Set(k))))
        }

      }
    Equation(key, result)
  }

  def contractEquation(paramIndex: Int, inValue: Value): Equation[Key, Value] = {
    val key = Key(method, InOut(paramIndex, inValue), resolveDirection)
    val result: Result[Key, Value] =
      if (exception || (inValue == Values.Null && interpreter.dereferencedParams(paramIndex)))
        Final(Values.Bot)
      else {
        returnValue match {
          case FalseValue() =>
            Final(Values.False)
          case TrueValue() =>
            Final(Values.True)
          case tr: Trackable if interpreter.dereferencedValues(tr.origin) =>
            Final(Values.NotNull)
          case TrackableNullValue(_) =>
            Final(Values.Null)
          case NotNullValue(_) | ThisValue() =>
            Final(Values.NotNull)
          case NthParamValue(_, `paramIndex`) =>
            Final(inValue)
          case TrackableCallValue(_, retType, m, stableCall, args, _) =>
            val isRefRetType = retType.getSort == Type.OBJECT || retType.getSort == Type.ARRAY
            var keys = Set[Key]()
            for ((NthParamValue(_, `paramIndex`), j) <- args.zipWithIndex) {
              keys += Key(m, InOut(j, inValue), stableCall)
            }
            if (isRefRetType) {
              keys += Key(m, Out, stableCall)
            }
            if (keys.nonEmpty)
              Pending[Key, Value](Set(Product(Values.Top, keys)))
            else
              Final(Values.Top)
          case _ =>
            Final(Values.Top)
        }
      }
    Equation(key, result)
  }

  def outContractEquation(): Equation[Key, Value] = {
    val key = Key(method, Out, resolveDirection)
    val result: Result[Key, Value] =
      if (exception) Final(Values.Bot)
      else {
        returnValue match {
          case FalseValue() =>
            Final(Values.False)
          case TrueValue() =>
            Final(Values.True)
          case tr: Trackable if interpreter.dereferencedValues(tr.origin) =>
            Final(Values.NotNull)
          case TrackableNullValue(_) =>
            Final(Values.Null)
          case NotNullValue(_) | ThisValue() =>
            Final(Values.NotNull)
          case TrackableCallValue(_, _, m, stableCall, args, _) =>
            val callKey = Key(m, Out, stableCall)
            Pending[Key, Value](Set(Product(Values.Top, Set(callKey))))
          case _ =>
            Final(Values.Top)
        }
      }
    Equation(key, result)
  }

  def nullableResultEquation(): Equation[Key, Value] = {
    val key = Key(method, Out, resolveDirection)
    val result: Result[Key, Value] =
      if (exception) Final(Values.Bot)
      else {
        returnValue match {
          case tr: Trackable if interpreter.dereferencedValues(tr.origin) =>
            Final(Values.Bot)
          case TrackableCallValue(_, _, m, resolveDir, args, callToThis) =>
            // TODO: when all solvers are refactored to 2-stage analysis, remove this specialization
            val callKey = Key(m, Out, CallUtils.specializeCallResolveDirection(resolveDir, callToThis))
            Pending[Key, Value](Set(Product(Values.Null, Set(callKey))))
          case TrackableNullValue(_) =>
            // it was not dereferenced
            Final(Values.Null)
          case _ =>
            Final(Values.Bot)
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
      val thisValue = ThisValue()
      frame.setLocal(local, thisValue)
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
class CombinedInterpreter(val insns: InsnList, arity: Int) extends BasicInterpreter {
  // Parameters dereferenced during execution of a method, tracked by parameter's indices.
  // Dereferenced parameters are @NotNull.
  val dereferencedParams = new Array[Boolean](arity)

  // Parameters, that are written to something or passed to an interface methods.
  // This parameters cannot be @Nullable.
  var notNullableParams = new Array[Boolean](arity)

  // parameterFlow(i) for i-th parameter stores a set parameter positions it is passed to
  // parameter is @NotNull if any of its usages are @NotNull
  var parameterFlow = Map[Int, Set[Key]]()

  // Trackable values that were dereferenced during execution of a method
  // Values are are identified by `origin` index
  val dereferencedValues = new Array[Boolean](insns.size())

  @inline
  final def index(insn: AbstractInsnNode) = insns.indexOf(insn)

  def track(origin: Int, bv: BasicValue): TrackableValue =
    if (bv == null) null else TrackableValue(origin, bv.getType)

  override def newOperation(insn: AbstractInsnNode): BasicValue = {
    val origin = index(insn)
    (insn.getOpcode: @switch) match {
      case ICONST_0 =>
        FalseValue()
      case ICONST_1 =>
        TrueValue()
      case ACONST_NULL =>
        TrackableNullValue(origin)
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
            track(origin, super.newOperation(insn))
        }
      case NEW =>
        NotNullValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc))
      case _ =>
        track(origin, super.newOperation(insn))
    }
  }

  override def unaryOperation(insn: AbstractInsnNode, value: BasicValue): BasicValue = {
    val origin = index(insn)
    (insn.getOpcode: @switch) match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER =>
        value match {
          case NthParamValue(_, n) =>
            dereferencedParams(n) = true
          case tr: Trackable =>
            dereferencedValues(tr.origin) = true
          case _ =>
        }
        track(origin, super.unaryOperation(insn, value))
      case CHECKCAST if value.isInstanceOf[NthParamValue] =>
        val nParam = value.asInstanceOf[NthParamValue]
        NthParamValue(Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc), nParam.n)
      case NEWARRAY | ANEWARRAY =>
        NotNullValue(super.unaryOperation(insn, value).getType)
      case _ =>
        track(origin, super.unaryOperation(insn, value))
    }
  }

  override def binaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue): BasicValue = {
    (insn.getOpcode: @switch) match {
      case PUTFIELD =>
        v1 match {
          case NthParamValue(_, n) =>
            dereferencedParams(n) = true
          case tr: Trackable =>
            dereferencedValues(tr.origin) = true
          case _ =>
        }
        if (v2.isInstanceOf[NthParamValue])
          notNullableParams(v2.asInstanceOf[NthParamValue].n) = true
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD =>
        v1 match {
          case NthParamValue(_, n) =>
            dereferencedParams(n) = true
          case tr: Trackable =>
            dereferencedValues(tr.origin) = true
          case _ =>
        }
      case _ =>
    }
    track(index(insn), super.binaryOperation(insn, v1, v2))
  }

  override def ternaryOperation(insn: AbstractInsnNode, v1: BasicValue, v2: BasicValue, v3: BasicValue): BasicValue = {
    (insn.getOpcode: @switch) match {
      case IASTORE | LASTORE | FASTORE | DASTORE | BASTORE | CASTORE | SASTORE =>
        v1 match {
          case NthParamValue(_, n) =>
            dereferencedParams(n) = true
          case tr: Trackable =>
            dereferencedValues(tr.origin) = true
          case _ =>
        }
      case AASTORE =>
        v1 match {
          case NthParamValue(_, n) =>
            dereferencedParams(n) = true
          case tr: Trackable =>
            dereferencedValues(tr.origin) = true
          case _ =>
        }
        if (v3.isInstanceOf[NthParamValue])
          notNullableParams(v3.asInstanceOf[NthParamValue].n) = true
      case _ =>
    }
    null
  }

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: BasicValue]): BasicValue = {
    val origin = index(insn)
    val opCode = insn.getOpcode
    val shift = if (opCode == INVOKESTATIC) 0 else 1
    // catching explicit dereferences
    if (opCode == INVOKESPECIAL || opCode == INVOKEINTERFACE || opCode == INVOKEVIRTUAL) {
      values.get(0) match {
        case NthParamValue(_, n) =>
          dereferencedParams(n) = true
        case tr: Trackable =>
          dereferencedValues(tr.origin) = true
        case _ =>
      }
    }
    (opCode: @switch) match {
      // catching implicit dereferences
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL | INVOKEINTERFACE =>
        val resolveDirection = CallUtils.callResolveDirection(opCode)
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
                val key = Key(method, In(i - shift), resolveDirection)
                parameterFlow = parameterFlow.updated(np.n, npKeys + key)
              }
            case _ =>
          }
        }
        val callToThis = (opCode == INVOKEINTERFACE || opCode == INVOKEVIRTUAL) && values.get(0).isInstanceOf[ThisValue]
        TrackableCallValue(origin, retType, method, resolveDirection, values.drop(shift).toList, callToThis)
      case MULTIANEWARRAY =>
        NotNullValue(super.naryOperation(insn, values).getType)
      case _ =>
        track(origin, super.naryOperation(insn, values))
    }

  }
}
