package faba.analysis

import scala.collection.mutable

import faba.cfg._
import faba.engine._
import scala.collection.immutable.IntMap

trait AState[C] {
  val stateIndex: Int
  val insnIndex: Int
  val conf: C
  val history: List[C]
}

abstract class Analysis[Id, Val:Lattice, Conf, State<:AState[Conf], Res] {

  sealed trait PendingAction
  case class ProceedState(state: State) extends PendingAction
  case class MakeResult(state: State, subResult: Res, indices: List[Int]) extends PendingAction

  val richControlFlow: RichControlFlow
  val controlFlow = richControlFlow.controlFlow
  val dfsTree = richControlFlow.dfsTree

  def createStartState(): State
  def combineResults(delta: Res, subResults: List[Res]): Res
  def mkEquation(result: Res): Equation[Id, Val]

  def confInstance(curr: Conf, prev: Conf): Boolean
  def stateInstance(curr: State, prev: State): Boolean
  def identity: Res

  def processState(state: State): Unit

  val pending =
    mutable.Stack[PendingAction]()
  // the key is insnIndex
  var computed =
    IntMap[List[State]]().withDefaultValue(Nil)
  // the key is stateIndex
  var results =
    IntMap[Res]()

  def analyze(): Equation[Id, Val] = {

    pending.push(ProceedState(createStartState()))

    while (pending.nonEmpty) pending.pop() match {
      case MakeResult(state, delta, subIndices) =>
        val result = combineResults(delta, subIndices.map(results))
        val insnIndex = state.insnIndex
        results = results + (state.stateIndex -> result)
        computed = computed.updated(insnIndex, state :: computed(insnIndex))
      case ProceedState(state) =>
        val stateIndex = state.stateIndex
        val insnIndex = state.insnIndex
        val conf = state.conf
        val history = state.history

        val loopEnter = dfsTree.loopEnters(insnIndex)
        val fold = loopEnter && history.exists(prevConf => confInstance(conf, prevConf))

        if (fold) {
          // folding
          results = results + (stateIndex -> identity)
          computed = computed.updated(insnIndex, state :: computed(insnIndex))
        } else computed(insnIndex).find(prevState => stateInstance(state, prevState)) match {
          case Some(ps) =>
            // sharing
            results = results + (stateIndex -> results(ps.stateIndex))
          case None =>
            // driving
            processState(state)
        }
    }

    mkEquation(results(0))
  }
}