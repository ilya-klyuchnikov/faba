package faba.analysis

import org.objectweb.asm.tree.analysis.{BasicValue, Frame}

/**
 * Utility class for analysis.
 */
object AnalysisUtils {

  def stateEquiv(curr: State, prev: State): Boolean =
    curr.constraint == prev.constraint && curr.conf.hashCode() == prev.conf.hashCode() &&
      equiv(curr.conf, prev.conf) &&
      curr.history.size == prev.history.size &&
      (curr.history, prev.history).zipped.forall((c1, c2) => c1.hashCode() == c2.hashCode() && equiv(c1, c2))

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
    case ParamInstanceOfCheckValue() => curr match {
      case ParamInstanceOfCheckValue() => true
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
    // TODO - is it safe to ignore origin of null value?
    case NullValue(_) => curr match {
      case NullValue(_) => true
      case _ => false
    }
    case NotNullValue(_) => curr match {
      case NotNullValue(_) => true
      case _ => false
    }
    // TODO - is it safe to ignore origin and type of call?
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
    if (curr.getClass == prev.getClass)
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
    else false

  def frameHashCode(frame: Frame[BasicValue]): Int = {
    var result = 0
    var i = 0
    var size = frame.getLocals
    while (i < size) {
      result = result * 31 + frame.getLocal(i).getClass.hashCode()
      i += 1
    }

    i = 0
    size = frame.getStackSize
    while (i < size) {
      result = result * 31 + frame.getStack(i).getClass.hashCode()
      i += 1
    }

    result
  }

  /**
   * get a value from the top of a stack
   *
   * @param frame frame
   * @return top of the stack of this frame
   */
  def popValue(frame: Frame[BasicValue]): BasicValue =
    frame.getStack(frame.getStackSize - 1)
}
