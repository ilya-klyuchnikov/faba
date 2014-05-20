package faba.analysis

import scala.collection.mutable
import scala.collection.immutable.IntMap

import faba.cfg._
import faba.data._
import faba.engine._
import org.objectweb.asm.tree.analysis.{BasicValue, Frame}
import org.objectweb.asm.Type

case class ParamValue(tp: Type) extends BasicValue(tp)
case class InstanceOfCheckValue() extends BasicValue(Type.INT_TYPE)
case class TrueValue() extends BasicValue(Type.INT_TYPE)
case class FalseValue() extends BasicValue(Type.INT_TYPE)
case class NullValue() extends BasicValue(Type.getObjectType("null"))
case class NotNullValue(tp: Type) extends BasicValue(tp)
case class CallResultValue(tp: Type, inters: Set[Key]) extends BasicValue(tp)

case class Conf(insnIndex: Int, frame: Frame[BasicValue])

case class State(index: Int, conf: Conf, history: List[Conf], taken: Boolean) {
  val insnIndex: Int = conf.insnIndex
}

abstract class Analysis[Res] {

  sealed trait PendingAction
  case class ProceedState(state: State) extends PendingAction
  case class MakeResult(state: State, subResult: Res, indices: List[Int]) extends PendingAction

  val richControlFlow: RichControlFlow
  val controlFlow = richControlFlow.controlFlow
  val dfsTree = richControlFlow.dfsTree

  def createStartState(): State
  def combineResults(delta: Res, subResults: List[Res]): Res
  def mkEquation(result: Res): Equation[Key, Value]

  def confInstance(curr: Conf, prev: Conf): Boolean
  def stateInstance(curr: State, prev: State): Boolean
  def identity: Res

  def processState(state: State): Unit

  val pending = mutable.Stack[PendingAction]()
  // the key is insnIndex
  var computed = IntMap[List[State]]().withDefaultValue(Nil)
  // the key is stateIndex
  var results = IntMap[Res]()

  def analyze(): Equation[Key, Value] = {
    pending.push(ProceedState(createStartState()))

    while (pending.nonEmpty) pending.pop() match {
      case MakeResult(state, delta, subIndices) =>
        val result = combineResults(delta, subIndices.map(results))
        val insnIndex = state.insnIndex
        results = results + (state.index -> result)
        computed = computed.updated(insnIndex, state :: computed(insnIndex))
      case ProceedState(state) =>
        val stateIndex = state.index
        val insnIndex = state.insnIndex
        val conf = state.conf
        val history = state.history

        val loopEnter = dfsTree.loopEnters(insnIndex)
        val fold = loopEnter && history.exists(prevConf => confInstance(conf, prevConf))

        if (fold) {
          results = results + (stateIndex -> identity)
          computed = computed.updated(insnIndex, state :: computed(insnIndex))
        } else computed(insnIndex).find(prevState => stateInstance(state, prevState)) match {
          case Some(ps) =>
            results = results + (stateIndex -> results(ps.index))
          case None =>
            processState(state)
        }
    }

    mkEquation(results(0))
  }
}