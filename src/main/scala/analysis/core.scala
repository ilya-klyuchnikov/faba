package faba.analysis

import faba.data._
import faba.engine._

import org.objectweb.asm.tree.MethodNode
import org.objectweb.asm.tree.analysis.{BasicValue, Frame}
import org.objectweb.asm.{Opcodes, Type}

/**
 * Control flow graph for a method's bytecode.
 *
 * @param transitions transitions(i) contains vertices reachable from i in one step
 * @param errorTransitions if (i -> j) is in errorTransitions,
 *                         then this transition corresponds to the enter into catch block
 * @param errors starts of catch blocks
 */
case class ControlFlowGraph(transitions: Array[List[Int]],
                            errorTransitions: Set[(Int, Int)],
                            errors: Array[Boolean])

/**
 * Output of a depth-first search of a control flow graph.
 * See [[http://en.wikipedia.org/wiki/Depth-first_search Depth-first search]].
 *
 * DFSTree is used for: testing reducibility of a graph, minimizing histories during analysis
 * (only loop enters are added to the history).
 *
 * @param preOrder preOrder list
 * @param postOrder postOrder list
 * @param spanningTree spanning edges (= tree edges)
 * @param backEdges back edges
 * @param loopEnters loopEnters(i) means that the ith node is an enter into the loop
 *
 */
case class DFSTree(preOrder: Array[Int],
                   postOrder: Array[Int],
                   spanningTree: Set[(Int, Int)],
                   backEdges: Set[(Int, Int)],
                   loopEnters: Array[Boolean]) {

  def isDescendant(child: Int, parent: Int): Boolean =
    preOrder(parent) <= preOrder(child) && postOrder(child) <= postOrder(parent)
}

/**
 * Lite analysis context. Used for Lite combined analysis.
 *
 * @param method method identifier
 * @param methodNode method's bytecode
 * @param controlFlow a control flow graph of the method's bytecode
 */
case class LiteContext(method: Method,
                       methodNode: MethodNode,
                       controlFlow: ControlFlowGraph)

/**
 * Analysis context. Used in complex analyses.
 *
 * @param method method identifier
 * @param methodNode method's bytecode
 * @param controlFlow a control flow graph of the method's bytecode
 * @param dfsTree method's depths-first search tree
 */
case class Context(method: Method,
                   methodNode: MethodNode,
                   controlFlow: ControlFlowGraph,
                   dfsTree: DFSTree)

/**
 * Marker annotation to denote data-class for some abstract value.
 * The reason for this annotation is to ease navigation and understanding of code.
 * Different values have different purposes and semantics explained in their documentation.
 *
 * FABA plugs into existing infrastructure of asm lib and extends
 * [[org.objectweb.asm.tree.analysis.Value]] and [[org.objectweb.asm.tree.analysis.BasicValue]] classes.
 */
class AsmAbstractValue extends scala.annotation.StaticAnnotation

/**
 * Trait for trackable values. Trackable values hold information about at which instruction it was created.
 * See `Trackable.origin` field.
 */
trait Trackable {
  /**
   * Instruction index at which a value was created
   */
  val origin: Int

  /**
   * Casts a trackable value to a given type. This method is used to execute CHECKCAST bytecode instruction.
   *
   * @param to type to cast trackable value to
   * @return the same (semantically) value, but casted to requested asm type
   */
  def cast(to: Type): BasicValue
}

/**
 * Abstract asm value for single parameter analyses (Parameter analysis and parameter->result analysis).
 * These analyses are: `@Nullable` parameter, `@NotNull` parameter, `@Contract(null->)`, `@Contract(!null->)`
 *
 * @param tp type of parameter
 */
@AsmAbstractValue case class ParamValue(tp: Type) extends BasicValue(tp)

/**
 * Abstract asm value to represent the result of `param instanceof SomeClass`.
 */
@AsmAbstractValue case class ParamInstanceOfCheckValue() extends BasicValue(Type.INT_TYPE)

/**
 * Abstract asm value to represent the value passed through nth parameter of a method.
 * Used in `@NotNull` and `@Contract(...)` inference.
 *
 * @param n parameter's in the list of parameters
 * @param tp parameter's type
 * @see `faba.contracts.InOutAnalysis#createStartValueForParameter(int, org.objectweb.asm.Type)`
 */
@AsmAbstractValue case class NThParamValue(n: Int, tp: Type) extends BasicValue(tp)

/**
 * Abstract asm value for `true` boolean constant.
 * Used for `@Contract(...->true|false)` inference
 */
@AsmAbstractValue case class TrueValue() extends BasicValue(Type.INT_TYPE)

/**
 * Abstract asm value for `false` boolean constant.
 * Used for `@Contract(...->true|false)` inference
 */
@AsmAbstractValue case class FalseValue() extends BasicValue(Type.INT_TYPE)

/**
 * Abstract asm value for representing value that are known to be not null at analysis time.
 * Such values appear for `NEW`, `NEWARRAY`, etc instructions and for `LDC` (load constant) instructions.
 *
 * @param tp asm type of value
 */
@AsmAbstractValue case class NotNullValue(tp: Type) extends BasicValue(tp)

/**
 * Abstract asm value for representing null values.
 * See `notes/null-value.md` for explanation of non-trivial fact "why is origin for null values".
 * @param origin instruction index at which a value was created
 */
@AsmAbstractValue case class NullValue(origin: Int) extends BasicValue(Type.getObjectType("null")) with Trackable {
  override def cast(tp: Type) = this
}

/**
 * Abstract asm value for representing the result of method invocations.
 *
 * @param origin instruction index at which a value was created
 * @param tp asm type of a value
 * @param inters all valuable keys
 */
@AsmAbstractValue case class CallResultValue(origin: Int, tp: Type, inters: Set[Key]) extends BasicValue(tp) with Trackable {
  override def cast(to: Type) = CallResultValue(origin, to, inters)
}

/**
 * Abstract asm value for representing values that we want to track to propagate nullity information.
 * Used for representing the result of execution following bytecode instructions:
 * `GETSTATIC`, `GETFIELD`, `AALOAD`.
 *
 * @param origin instruction index at which a value was created
 * @param tp asm type of a value
 */
@AsmAbstractValue case class TrackableBasicValue(origin: Int, tp: Type) extends BasicValue(tp) with Trackable {
  override def cast(to: Type) = TrackableBasicValue(origin, to)
}

case class Conf(insnIndex: Int, frame: Frame[BasicValue]) {
  val frameHashCode = AnalysisUtils.frameHashCode(frame)
  override def hashCode() = frameHashCode
}

/**
 * Program point considered by analysis.
 *
 * Note about constraints: it turns out, that representation of constraints as a bit mask
 * provides quite good performance.
 *
 * @param index unique index of state. Used as identity.
 * @param conf configuration of this program point.
 * @param history history - ancestors of a current configuration
 * @param constraint constraint encoded as int bit-mask.
 */
case class State(index: Int, conf: Conf, history: List[Conf], constraint: Int)

/**
 * Skeleton for implementing staged analysis via exploration of graph of configurations.
 */
abstract class StagedScAnalysis {
  val context: Context
  val direction: Direction

  import context._
  // specification (index) equation is valid for Upward resolve direction only
  val aKey = Key(method, direction, ResolveDirection.Upward)

  /**
   * Performs one step of analysis. The implied result of this method is side-effect.
   *
   * @param state current state (program point with some history)
   */
  def processState(state: State): Unit

  /**
   * Constructs a negative equation for an early result.
   * @return negative equation for an early result
   */
  def earlyEquation(): Equation[Key, Value] =
    Equation(aKey, Final(Values.Top))

  /**
   * Bookkeeping of already analyzed states.
   * `computed(i)` is a set of already analyzed states having `state.conf.insnIndex = i`
   * (the key is insnIndex)
   */
  val computed = Array.tabulate[List[State]](methodNode.instructions.size()){i => Nil}

  /**
   * Part of analysis state.
   * Quite often during analysis it is possible to identify the negative result of analysis
   * without processing the whole graph of configurations.
   * If such situation is encountered, `earlyResult` may be set to `true`.
   * `earlyResult` is checked at each step of analysis.
   *
   * @see [[faba.analysis.result.ResultAnalysis#analyze()]]
   * @see [[faba.analysis.parameters.NotNullParameterAnalysis#analyze()]]
   * @see [[faba.analysis.parameters.NullableParameterAnalysis#analyze()]]
   */
  var earlyResult: Boolean = false

  // internal counter for creating monotone ids
  private var id = 0

  /**
   * Generates new unique id.
   *
   * @return new unique id.
   */
  @throws[LimitReachedException]("when graph of configurations is too big")
  final def genId(): Int = {
    id += 1
    if (id > stepsLimit) throw new LimitReachedException
    id
  }

  /**
   * Utility method for creating start state for analysis.
   *
   * @return start state for analysis
   */
  final def createStartState(): State =
    State(0, Conf(0, createStartFrame()), Nil, 0)

  /**
   * Creates start frame for analysis.
   *
   * @return start frame for analysis
   * @see `createStartState`
   * @see `createStartValueForParameter`
   */
  final def createStartFrame(): Frame[BasicValue] = {
    val frame = new Frame[BasicValue](methodNode.maxLocals, methodNode.maxStack)
    val returnType = Type.getReturnType(methodNode.desc)
    val returnValue = if (returnType == Type.VOID_TYPE) null else new BasicValue(returnType)
    frame.setReturn(returnValue)

    val args = Type.getArgumentTypes(methodNode.desc)
    var local = 0
    if ((methodNode.access & Opcodes.ACC_STATIC) == 0) {
      val basicValue = new NotNullValue(Type.getObjectType(method.internalClassName))
      frame.setLocal(local, basicValue)
      local += 1
    }
    for (i <- 0 until args.size) {
      val value = direction match {
        case InOut(`i`, _) | In(`i`) =>
          new ParamValue(args(i))
        case _ =>
          createStartValueForParameter(i, args(i))
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

  /**
   * Creates initial value for parameter. Intended to be overridden/customized.
   * The default implementation returns {{{BasicValue(tp)}}}.
   *
   * @param i parameter's index
   * @param tp parameter's type
   * @return Abstract value to be used as a starting point for analysis.
   * @see `createStartFrame`
   * @see `InOutAnalysis.createStartValueForParameter`
   */
  def createStartValueForParameter(i: Int, tp: Type): BasicValue =
    new BasicValue(tp)
}
