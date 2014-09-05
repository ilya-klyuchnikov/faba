package faba.fastAnalysis

import faba.asm.{FastFrame, FastValues}
import org.objectweb.asm.{Opcodes, Type}

import faba.cfg._
import faba.data._
import faba.engine._

case class Conf(insnIndex: Int, frame: FastFrame) {
  val _hashCode = frame.hashCode()
  override def hashCode() = _hashCode
}

case class State(index: Int, conf: Conf, history: List[Conf], taken: Boolean, hasCompanions: Boolean)

object LimitReachedException {
  // elementary steps limit
  val limit = 1 << 15
}

class LimitReachedException extends Exception("Limit reached exception")

object Analysis {
  sealed trait PendingAction[+Res]
  case class ProceedState(state: State) extends PendingAction[Nothing]
  case class MakeResult[Res](states: List[State], subResult: Res, indices: List[Int]) extends PendingAction[Res]

  val ourPending = new Array[State](LimitReachedException.limit)
}

abstract class Analysis[Res] {

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
    curr.taken == prev.taken && Utils.equiv(curr.conf, prev.conf) && Utils.equivHistory(curr.history, prev.history)

  // the key is insnIndex
  var computed = Array.tabulate[List[State]](methodNode.instructions.size()){i => Nil}
  // the key is stateIndex
  var earlyResult: Option[Res] = None

  private var id = 0
  @inline
  final def mkId(): Int = {
    id += 1
    if (id > LimitReachedException.limit) throw new LimitReachedException
    id
  }
  final def lastId(): Int = id

  final def createStartFrame(): FastFrame = {
    val frame = new FastFrame(methodNode.maxLocals, methodNode.maxStack)
    val args = Type.getArgumentTypes(methodNode.desc)
    var local = 0
    if ((methodNode.access & Opcodes.ACC_STATIC) == 0) {
      frame.setLocal(local, FastValues.ANY_VAL)
      local += 1
    }
    for (i <- 0 until args.size) {
      val argSize = args(i).getSize
      val value = direction match {
        case In(`i`) =>
          FastValues.PARAM_VAL
        case _ =>
          if (argSize == 1) FastValues.ANY_VAL else FastValues.DOUBLE_OR_LONG
      }
      frame.setLocal(local, value)
      local += 1
      if (argSize == 2) {
        frame.setLocal(local, FastValues.ANY_VAL)
        local += 1
      }
    }
    while (local < methodNode.maxLocals) {
      frame.setLocal(local, FastValues.ANY_VAL)
      local += 1
    }
    frame
  }

  final def popValue(frame: FastFrame): Int =
    if (frame.getStackSize == 0) FastValues.ANY_VAL else frame.getStack(frame.getStackSize - 1)
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

  def isInstance(curr: Int, prev: Int): Boolean = {
    if (prev == FastValues.PARAM_VAL || prev == FastValues.INSTANCE_OF_CHECK_VAL)
      prev == curr
    else
      true
  }

  def equiv(curr: Conf, prev: Conf): Boolean =
    curr._hashCode == prev._hashCode && curr.frame == prev.frame

  def equivHistory(history1: List[Conf], history2: List[Conf]): Boolean = {
    if (history1.size != history2.size) {
      return false
    }
    var h1 = history1
    var h2 = history1
    while (h1.nonEmpty) {
      if (!equiv(h1.head, h2.head))
        return false
      h1 = h1.tail
      h2 = h2.tail
    }
    true
  }
}
