package faba.analysis

import org.objectweb.asm.tree.analysis.{BasicValue, Frame}
import org.objectweb.asm.{Opcodes, Type}

import faba.cfg._
import faba.data._
import faba.engine._

trait Trackable {
  val origin: Int
  def cast(to: Type): BasicValue
}

case class ParamValue(tp: Type) extends BasicValue(tp)
case class InstanceOfCheckValue() extends BasicValue(Type.INT_TYPE)
case class NThParamValue(n: Int, tp: Type) extends BasicValue(tp)
case class TrueValue() extends BasicValue(Type.INT_TYPE)

case class FalseValue() extends BasicValue(Type.INT_TYPE)
case class NotNullValue(tp: Type) extends BasicValue(tp)

case class NullValue(origin: Int) extends BasicValue(Type.getObjectType("null")) with Trackable {
  override def cast(tp: Type) = this
}
case class CallResultValue(origin: Int, tp: Type, inters: Set[Key]) extends BasicValue(tp) with Trackable {
  override def cast(to: Type) = CallResultValue(origin, to, inters)
}
case class TrackableBasicValue(origin: Int, tp: Type) extends BasicValue(tp) with Trackable {
  override def cast(to: Type) = TrackableBasicValue(origin, to)
}

case class Conf(insnIndex: Int, frame: Frame[BasicValue]) {
  lazy val _hashCode = {
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

// TODO - is it correct to consider history as history of configurations only
// TODO - not as history of states?
/**
 * Program point considered by analysis.
 *
 * @param index unique index of state. Used as identity.
 * @param conf configuration of this program point.
 * @param history history - ancestors of a current configuration
 * @param constraint constraint encoded as int bit-mask.
 */
case class State(index: Int, conf: Conf, history: List[Conf], constraint: Int)

object LimitReachedException {
  // elementary steps limit
  val limit = 1 << 15
}

class LimitReachedException extends Exception("Limit reached exception")

/**
 * Skeleton for implementing analysis via exploration of graph of configurations.
 * All analyses are implemented by following scenario:
 *
 * During construction of a graph of configurations, some internal result `Res` is constructed.
 * Then this internal `Res` is translated into equation.
 *
 * @tparam Res internal Result of analysis.
 *
 * @see `mkEquation(result: Res): Equation[Key, Value]`
 */
abstract class Analysis[Res] {

  val richControlFlow: RichControlFlow
  val direction: Direction
  val stable: Boolean
  val controlFlow = richControlFlow.controlFlow
  val methodNode = controlFlow.methodNode
  val method = Method(controlFlow.className, methodNode.name, methodNode.desc)
  val dfsTree = richControlFlow.dfsTree
  val aKey = Key(method, direction, stable)

  /**
   * Performs one step of analysis. The implied result of this method is side-effect.
   *
   * @param state current state (program point with some history)
   */
  def processState(state: State): Unit

  /**
   * Transforms an internal result of analysis into a corresponding equation.
   * When exploration of a graph of configurations is finished,
   * this method is called to gen an equation.
   *
   * @param result internal result
   * @return
   */
  def mkEquation(result: Res): Equation[Key, Value]

  final def createStartState(): State =
    State(0, Conf(0, createStartFrame()), Nil, 0)
  final def confInstance(curr: Conf, prev: Conf): Boolean =
    Utils.isInstance(curr, prev)

  /**
   * Bookkeeping of already analyzed states.
   * `computed(i)` is a set of already analyzed states having `state.conf.insnIndex = i`
   * (the key is insnIndex)
   */
  val computed = Array.tabulate[List[State]](methodNode.instructions.size()){i => Nil}

  /**
   * Part of analysis state.
   * Quite often during analysis it is possible to identify the result of analysis
   * without processing the whole graph of configurations.
   * If such situation is encountered, `earlyResult` may be set to `Some(result)`.
   * `earlyResult` is checked at each step of analysis.
   *
   * @see [[faba.contracts.InOutAnalysis#analyze()]]
   * @see [[faba.parameters.NotNullInAnalysis.analyze()]]
   * @see [[faba.parameters.NullableInAnalysis.analyze()]]
   */
  var earlyResult: Option[Res] = None

  private var id = 0
  @inline
  final def mkId(): Int = {
    id += 1
    if (id > LimitReachedException.limit) throw new LimitReachedException
    id
  }
  final def lastId(): Int = id

  def createStartFrame(): Frame[BasicValue] = {
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
  final def stateEquiv(curr: State, prev: State): Boolean =
    curr.constraint == prev.constraint && curr.conf.hashCode() == prev.conf.hashCode() &&
      Utils.equiv(curr.conf, prev.conf) &&
      curr.history.size == prev.history.size &&
      (curr.history, prev.history).zipped.forall((c1, c2) => c1.hashCode() == c2.hashCode() && Utils.equiv(c1, c2))

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
    // TODO - is it safe??
    case NullValue(_) => curr match {
      case NullValue(_) => true
      case _ => false
    }
    case NotNullValue(_) => curr match {
      case NotNullValue(_) => true
      case _ => false
    }
    // TODO - is it safe??
    case CallResultValue(_, _, prevInters) => curr match {
      case CallResultValue(_, _, currInters) => currInters == prevInters
      case _ => false
    }
    case _: BasicValue => true
  }

  def equiv(curr: Conf, prev: Conf): Boolean = {
    val currFr = curr.frame
    val prevFr = prev.frame
    for (i <- (currFr.getStackSize - 1) to 0 by -1 if !equiv(currFr.getStack(i), prevFr.getStack(i)))
      return false
    for (i <- (currFr.getLocals - 1) to 0 by -1 if !equiv(currFr.getLocal(i), prevFr.getLocal(i)))
      return false
    true
  }

  def equiv(curr: BasicValue, prev: BasicValue): Boolean =
    if (curr.getClass == prev.getClass) {
      (curr, prev) match {
        case (CallResultValue(_, _, k1), CallResultValue(_, _, k2)) =>
          k1 == k2
        case (tr1: Trackable, tr2: Trackable) =>
          tr1.origin == tr2.origin
        case (NThParamValue(n1, _), NThParamValue(n2, _)) =>
          n1 == n2
        case _ =>
          true
      }
    }
    else false

}
