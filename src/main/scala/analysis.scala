package faba.analysis

import scala.collection.mutable
import scala.collection.immutable.IntMap

import org.objectweb.asm.{Opcodes, Type}
import org.objectweb.asm.tree.{VarInsnNode, AbstractInsnNode}
import org.objectweb.asm.tree.analysis.{Interpreter, BasicValue, Frame}

import faba.cfg._
import faba.data._
import faba.engine._

case class ParamValue(tp: Type) extends BasicValue(tp)
case class InstanceOfCheckValue() extends BasicValue(Type.INT_TYPE)

case class TrueValue() extends BasicValue(Type.INT_TYPE)
case class FalseValue() extends BasicValue(Type.INT_TYPE)
case class NullValue() extends BasicValue(Type.getObjectType("null"))
case class NotNullValue(tp: Type) extends BasicValue(tp)
case class CallResultValue(tp: Type, inters: Set[Key]) extends BasicValue(tp)

// frame to track locals -> stack correspondence
class SmartFrame[V <: org.objectweb.asm.tree.analysis.Value](locals: Int, stack: Int) extends Frame[V](locals, stack) {
  var mapping: List[Int] = Nil

  def this(f: SmartFrame[V]) {
    this(f.getLocals, f.getMaxStackSize)
    init(f)
    mapping = f.mapping
  }

  override def execute(insn: AbstractInsnNode, interpreter: Interpreter[V]): Unit = {
    insn.getOpcode match {
      case Opcodes.ALOAD =>
        val local = insn.asInstanceOf[VarInsnNode].`var`
        push(interpreter.copyOperation(insn, getLocal(local)), local)
      case _ =>
        super.execute(insn, interpreter)
    }
  }

  override def push(value: V): Unit = {
    super.push(value)
    mapping = -1 :: mapping
  }

  override def pop(): V = {
    mapping = mapping.tail
    super.pop()
  }

  def push(value: V, local: Int): Unit = {
    super.push(value)
    mapping = local :: mapping
  }

  override def clearStack(): Unit = {
    super.clearStack()
    mapping = Nil
  }

  override def setLocal(i: Int, value: V): Unit = {
    mapping = mapping.map(j => if (j == i) -1 else j)
    super.setLocal(i, value)
  }
}

case class Conf(insnIndex: Int, frame: SmartFrame[BasicValue]) {
  val _hashCode = {
    var result = 0
    for (i <- 0 until frame.getLocals) {
      result = result * 31 + frame.getLocal(i).getClass.hashCode()
    }
    for (i <- 0 until frame.getStackSize) {
      result = result * 31 + frame.getStack(i).getClass.hashCode()
    }
    result
  }
  override def hashCode() = _hashCode
}

case class State(index: Int, conf: Conf, history: List[Conf], taken: Boolean, hasCompanions: Boolean)

abstract class Analysis[Res] {

  sealed trait PendingAction
  case class ProceedState(state: State) extends PendingAction
  case class MakeResult(states: List[State], subResult: Res, indices: List[Int]) extends PendingAction

  val richControlFlow: RichControlFlow
  val direction: Direction
  val stable: Boolean
  def identity: Res
  def processState(state: State): Unit
  def isEarlyResult(res: Res): Boolean
  def combineResults(delta: Res, subResults: List[Res]): Res
  def mkEquation(result: Res): Equation[Key, Value]

  val controlFlow = richControlFlow.controlFlow
  val methodNode = controlFlow.methodNode
  val method = Method(controlFlow.className, methodNode.name, methodNode.desc)
  val dfsTree = richControlFlow.dfsTree
  val aKey = Key(method, direction, stable)

  final def createStartState(): State = State(0, Conf(0, createStartFrame()), Nil, false, false)
  final def confInstance(curr: Conf, prev: Conf): Boolean = Utils.isInstance(curr, prev)

  final def stateEquiv(curr: State, prev: State): Boolean =
    curr.taken == prev.taken && curr.conf.hashCode() == prev.conf.hashCode() &&
      Utils.equiv(curr.conf, prev.conf) &&
      curr.history.size == prev.history.size &&
      (curr.history, prev.history).zipped.forall((c1, c2) => c1.hashCode() == c2.hashCode() && Utils.equiv(c1, c2))

  val pending = mutable.Stack[PendingAction]()
  // the key is insnIndex
  var computed = IntMap[List[State]]().withDefaultValue(Nil)
  // the key is stateIndex
  var results = IntMap[Res]()

  var earlyResult: Option[Res] = None

  private var id = 0
  @inline
  final def mkId(): Int = {
    id += 1; id
  }

  final def lastId(): Int = id

  final def analyze(): Equation[Key, Value] = {
    pending.push(ProceedState(createStartState()))

    while (pending.nonEmpty && earlyResult.isEmpty) pending.pop() match {
      case MakeResult(states, delta, subIndices) =>
        val result = combineResults(delta, subIndices.map(results))
        if (isEarlyResult(result)) {
          earlyResult = Some(result)
        } else {
          // updating all results
          for (state <- states) {
            val insnIndex = state.conf.insnIndex
            results = results + (state.index -> result)
            computed = computed.updated(insnIndex, state :: computed(insnIndex))
          }
        }
      case ProceedState(state) =>
        processState(state)
    }

    mkEquation(earlyResult.getOrElse(results(0)))
  }

  final def createStartFrame(): SmartFrame[BasicValue] = {
    val frame = new SmartFrame[BasicValue](methodNode.maxLocals, methodNode.maxStack)
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
      val value = direction match {
        case InOut(`i`, _) =>
          new ParamValue(args(i))
        case In(`i`) =>
          new ParamValue(args(i))
        case _ =>
          new BasicValue(args(i))
      }
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

  final def popValue(frame: Frame[BasicValue]): BasicValue =
    frame.getStack(frame.getStackSize - 1)
}

object Utils {
  def isInstance(curr: Conf, prev: Conf): Boolean = {
    if (curr.insnIndex != prev.insnIndex) {
      return false
    }
    val currFr = curr.frame
    val prevFr = prev.frame
    for (i <- 0 until currFr.getLocals if !isInstance(currFr.getLocal(i), prevFr.getLocal(i)))
      return false
    for (i <- 0 until currFr.getStackSize if !isInstance(currFr.getStack(i), prevFr.getStack(i)))
      return false
    true
  }

  def isInstance(curr: BasicValue, prev: BasicValue): Boolean = prev match {
    case (_: ParamValue) => curr match {
      case _: ParamValue => true
      case _ => false
    }
    case InstanceOfCheckValue() => curr match {
      case InstanceOfCheckValue() => true
      case _ => false
    }
    case TrueValue() => curr match {
      case TrueValue() => true
      case _ => false
    }
    case FalseValue() => curr match {
      case FalseValue() => true
      case _ => false
    }
    case NullValue() => curr match {
      case NullValue() => true
      case _ => false
    }
    case NotNullValue(_) => curr match {
      case NotNullValue(_) => true
      case _ => false
    }
    case CallResultValue(_, prevInters) => curr match {
      case CallResultValue(_, currInters) => currInters == prevInters
      case _ => false
    }
    case _: BasicValue => true
  }

  def equiv(curr: Conf, prev: Conf): Boolean = {
    val currFr = curr.frame
    val prevFr = prev.frame
    if (currFr.mapping != prevFr.mapping)
      return false
    for (i <- (currFr.getStackSize - 1) to 0 by -1 if !equiv(currFr.getStack(i), prevFr.getStack(i)))
      return false
    for (i <- (currFr.getLocals - 1) to 0 by -1 if !equiv(currFr.getLocal(i), prevFr.getLocal(i)))
      return false
    true
  }

  def equiv(curr: BasicValue, prev: BasicValue): Boolean =
    if (curr.getClass == prev.getClass) {
      (curr, prev) match {
        case (CallResultValue(_, k1), CallResultValue(_, k2)) =>
          k1 == k2
        case _ =>
          true
      }
    }
    else false

}
