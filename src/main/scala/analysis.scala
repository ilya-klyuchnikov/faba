package faba.analysis

import scala.collection.mutable
import scala.collection.immutable.IntMap

import faba.cfg._
import faba.data._
import faba.engine._
import org.objectweb.asm.tree.analysis.{BasicValue, Frame}
import org.objectweb.asm.{Opcodes, Type}

case class ParamValue(tp: Type) extends BasicValue(tp)
case class InstanceOfCheckValue() extends BasicValue(Type.INT_TYPE)
case class TrueValue() extends BasicValue(Type.INT_TYPE)
case class FalseValue() extends BasicValue(Type.INT_TYPE)
case class NullValue() extends BasicValue(Type.getObjectType("null"))
case class NotNullValue(tp: Type) extends BasicValue(tp)
case class CallResultValue(tp: Type, inters: Set[Key]) extends BasicValue(tp)

case class Conf(insnIndex: Int, frame: Frame[BasicValue])

case class State(index: Int, conf: Conf, history: List[Conf], taken: Boolean, hasCompanions: Boolean) {
  val insnIndex: Int = conf.insnIndex
}

abstract class Analysis[Res] {

  sealed trait PendingAction
  case class ProceedState(state: State) extends PendingAction
  case class MakeResult(state: State, subResult: Res, indices: List[Int]) extends PendingAction

  val richControlFlow: RichControlFlow
  val direction: Direction
  val controlFlow = richControlFlow.controlFlow
  val methodNode = controlFlow.methodNode
  val method = Method(controlFlow.className, methodNode.name, methodNode.desc)
  val dfsTree = richControlFlow.dfsTree
  val aKey = Key(method, direction)

  def createStartState(): State = State(0, Conf(0, createStartFrame()), Nil, false, false)
  def combineResults(delta: Res, subResults: List[Res]): Res
  def mkEquation(result: Res): Equation[Key, Value]

  def confInstance(curr: Conf, prev: Conf): Boolean
  def stateInstance(curr: State, prev: State): Boolean
  def identity: Res

  def processState(state: State): Unit
  def isEarlyResult(res: Res): Boolean

  val pending = mutable.Stack[PendingAction]()
  // the key is insnIndex
  var computed = IntMap[List[State]]().withDefaultValue(Nil)
  // the key is stateIndex
  var results = IntMap[Res]()

  var earlyResult: Option[Res] = None

  final def analyze(): Equation[Key, Value] = {
    pending.push(ProceedState(createStartState()))

    while (pending.nonEmpty && earlyResult.isEmpty) pending.pop() match {
      case MakeResult(state, delta, subIndices) =>
        val result = combineResults(delta, subIndices.map(results))
        if (isEarlyResult(result)) {
          earlyResult = Some(result)
        } else {
          val insnIndex = state.insnIndex
          results = results + (state.index -> result)
          computed = computed.updated(insnIndex, state :: computed(insnIndex))
        }
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

    mkEquation(earlyResult.getOrElse(results(0)))
  }

  final protected def createStartFrame(): Frame[BasicValue] = {
    val frame = new Frame[BasicValue](methodNode.maxLocals, methodNode.maxStack)
    val returnType = Type.getReturnType(methodNode.desc)
    val returnValue = if (returnType == Type.VOID_TYPE) null else new BasicValue(returnType)
    frame.setReturn(returnValue)

    val args = Type.getArgumentTypes(methodNode.desc)
    var local = 0
    if ((methodNode.access & Opcodes.ACC_STATIC) == 0) {
      val basicValue = new BasicValue(Type.getObjectType(controlFlow.className))
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
