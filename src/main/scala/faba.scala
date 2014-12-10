package faba

import faba.analysis._
import faba.analysis.leakingParameters._
import faba.analysis.nullableResult._
import faba.analysis.parameters._
import faba.analysis.purity._
import faba.analysis.result._
import faba.analysis.resultInfluence._
import faba.analysis.resultOrigins._
import faba.analysis.combined._

import faba.calls._
import faba.data._
import faba.engine._
import faba.source._

import org.objectweb.asm.Opcodes._
import org.objectweb.asm._
import org.objectweb.asm.tree.MethodNode
import org.objectweb.asm.tree.analysis.{Frame, Value => ASMValue}

import scala.language.existentials

/**
 * Context to memoize expensive (to some extend) computations.
 *
 * @param referenceResult true if the method type is reference
 * @param booleanResult true if the method type is boolean
 * @param parameterTypes types of method parameters
 */
case class ExtraContext(referenceResult: Boolean,
                        booleanResult: Boolean,
                        parameterTypes: Array[Type])

/**
 * Default faba processor. A lot of fine-grained method to override.
 **/
trait FabaProcessor extends Processor {

  /**
   * Setting for benchmarking.
   * If [[idle]] is true, then FABA doesn't solve equations.
   * May be useful to set [[idle]] to true when you would like to measure/optimize performance of analysis.
   */
  @inline
  final val idle = false

  var extras = Map[Method, MethodExtra]()
  var complexTime: Long = 0
  var nonCycleTime: Long = 0
  var cycleTime: Long = 0
  var nonCycleMethods: Long = 0
  var cycleMethods: Long = 0
  var simpleTime: Long = 0
  var complexMethods: Long = 0
  var simpleMethods: Long = 0

  override def processClass(classReader: ClassReader): Unit =
    classReader.accept(new ClassVisitor(ASM5) {
      var stableClass = false
      var classInfo: ClassInfo = _

      override def visit(version: Int, access: Int, name: String, signature: String, superName: String, interfaces: Array[String]) {
        stableClass = (access & ACC_FINAL) != 0
        classInfo = ClassInfo(access, classReader.getClassName, superName, interfaces.toList)
        super.visit(version, access, name, signature, superName, interfaces)
        mapClassInfo(this.classInfo)
      }

      override def visitMethod(access: Int, name: String, desc: String, signature: String, exceptions: Array[String]) = {
        val node = new MethodNode(ASM5, access, name, desc, signature, exceptions)

        new MethodVisitor(ASM5, node) {
          var jsr = false
          override def visitEnd(): Unit = {
            super.visitEnd()
            mapMethodInfo(MethodInfo(classInfo, access, name, desc))
            processMethod(classReader.getClassName, node, stableClass, jsr)
          }

          override def visitJumpInsn(opcode: Int, label: Label) {
            if (opcode == Opcodes.JSR)
              jsr = true
            super.visitJumpInsn(opcode, label)
          }
        }
      }
    }, ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES)

  def processMethod(className: String, methodNode: MethodNode, stableClass: Boolean, jsr: Boolean) {
    val argumentTypes = Type.getArgumentTypes(methodNode.desc)
    val resultType = Type.getReturnType(methodNode.desc)
    val resultSort = resultType.getSort

    val isReferenceResult = resultSort == Type.OBJECT || resultSort == Type.ARRAY
    val isBooleanResult = Type.BOOLEAN_TYPE == resultType

    val method = Method(className, methodNode.name, methodNode.desc)

    if (!idle)
      extras = extras.updated(method, MethodExtra(Option(methodNode.signature), methodNode.access))

    purityEquation(method, methodNode).foreach(handlePurityEquation)

    if (argumentTypes.length == 0 && !(isReferenceResult || isBooleanResult)) {
      return
    }

    var added = false
    val graph = buildCFG(className, methodNode, jsr)

    if (graph.transitions.nonEmpty) {
      val dfs = buildDFSTree(graph.transitions)
      val complex = dfs.backEdges.nonEmpty || graph.transitions.exists(_.size > 1)
      val start = System.nanoTime()
      if (complex) {
        val reducible = dfs.backEdges.isEmpty || isReducible(graph, dfs)
        if (reducible) {
          handleComplexMethod(method, className, methodNode, dfs, argumentTypes, graph, isReferenceResult, isBooleanResult, jsr)
          added = true
        }
      } else {
        val context = LiteContext(method, methodNode, graph)
        val extraContext = ExtraContext(isReferenceResult, isBooleanResult, argumentTypes)
        handleSimpleMethod(context, extraContext)
        added = true
      }
      val time = System.nanoTime() - start
      if (complex) {
        complexMethods += 1
        complexTime += time
      }
      else {
        simpleMethods += 1
        simpleTime += time
      }
    }


    if (!added) {
      for (i <- argumentTypes.indices) {
        val argType = argumentTypes(i)
        val argSort = argType.getSort
        val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
        if (isReferenceArg) {
          handleNotNullParamEquation(Equation(Key(method, In(i), ResolveDirection.Upward), Final(Values.Top)))
          if (isReferenceResult || isBooleanResult) {
            handleNullContractEquation(Equation(Key(method, InOut(i, Values.Null), ResolveDirection.Upward), Final(Values.Top)))
            handleNotNullContractEquation(Equation(Key(method, InOut(i, Values.NotNull), ResolveDirection.Upward), Final(Values.Top)))
          }
        }
      }
      if (isReferenceResult) {
        handleOutContractEquation(Equation(Key(method, Out, ResolveDirection.Upward), Final(Values.Top)))
        handleNullableResultEquation(Equation(Key(method, Out, ResolveDirection.Upward), Final(Values.Bot)))
      }
    }
  }

  /**
   * handles linear methods (without branching in control flow)
   * @param context
   * @param extraContext
   */
  def handleSimpleMethod(context: LiteContext, extraContext: ExtraContext) {
    import extraContext._

    val analyzer = new CombinedSingleAnalysis(context)

    // analyzer pass
    analyzer.analyze()

    // getting equations from analyzer
    if (extraContext.referenceResult) {
      handleOutContractEquation(analyzer.outContractEquation())
      handleNullableResultEquation(analyzer.nullableResultEquation())
    }
    for (i <- parameterTypes.indices) {
      val argSort = parameterTypes(i).getSort
      val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
      if (isReferenceArg) {
        handleNotNullParamEquation(analyzer.notNullParamEquation(i))
        handleNullableParamEquation(analyzer.nullableParamEquation(i))
        // contracts
        if (referenceResult || booleanResult) {
          handleNullContractEquation(analyzer.contractEquation(i, Values.Null))
          handleNotNullContractEquation(analyzer.contractEquation(i, Values.NotNull))
        }
      }
    }
  }

  def handleComplexMethod(method: Method,
                          className: String,
                          methodNode: MethodNode,
                          dfs: DFSTree,
                          argumentTypes: Array[Type],
                          graph: ControlFlowGraph,
                          isReferenceResult: Boolean,
                          isBooleanResult: Boolean,
                          jsr: Boolean) {
    val start = System.nanoTime()
    val cycle = dfs.backEdges.nonEmpty
    // leaking params will be taken for further decisions
    lazy val leaking = leakingParameters(className, methodNode, jsr)
    lazy val resultOrigins = buildResultOrigins(className, methodNode, leaking.frames, graph)
    lazy val parameterToResult = ParameterToResultFlow.analyze(methodNode, leaking, resultOrigins)
    //val context =  Context(method, methodNode, graph, resolveDirection, dfs)
    val context =  Context(method, methodNode, graph, dfs)

    // todo - do we need equations for boolean results?
    lazy val resultEquation: Equation[Key, Value] = outContractEquation(context, resultOrigins)
    if (isReferenceResult) {
      handleOutContractEquation(resultEquation)
      handleNullableResultEquation(nullableResultEquation(className, methodNode, method, resultOrigins, jsr))
    }
    for (i <- argumentTypes.indices) {
      val argType = argumentTypes(i)
      val argSort = argType.getSort
      val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY

      if (isReferenceArg) {
        // have we discovered that param is @NotNull now?
        var notNullParam = false
        // an execution path was discovered at which this param is dereferenced
        var dereferenceFound = false

        // [[[ parameter analysis
        if (leaking.parameters(i)) {
          val (notNullParamEq, npe) = notNullParamEquation(context, i)
          notNullParam = notNullParamEq.rhs == Final(Values.NotNull)
          if (notNullParam || npe) {
            dereferenceFound = true
          }
          handleNotNullParamEquation(notNullParamEq)
        }
        else
          handleNotNullParamEquation(Equation(Key(method, In(i), ResolveDirection.Upward), Final(Values.Top)))

        if (leaking.nullableParameters(i)) {
          if (dereferenceFound) {
            handleNullableParamEquation(Equation(Key(method, In(i), ResolveDirection.Upward), Final(Values.Top)))
          }
          else {
            val nullableParamEq = nullableParamEquation(context, i)
            if (nullableParamEq.rhs == Final(Values.Top)) {
              dereferenceFound = true
            }
            handleNullableParamEquation(nullableParamEq)
          }
        }
        else
          handleNullableParamEquation(Equation(Key(method, In(i), ResolveDirection.Upward), Final(Values.Null)))
        // ]]] parameter analysis

        // [[[ contract analysis
        if (isReferenceResult || isBooleanResult) {
          val paramInfluence = leaking.splittingParameters(i) || parameterToResult(i)
          // result may depend on a parameter
          if (leaking.parameters(i)) {
            val unconditionalDereference = dereferenceFound && !leaking.splittingParameters(i) && !resultOrigins.parameters(i)
            // [[[ null->... analysis
            if (notNullParam) {
              handleNullContractEquation(Equation(Key(method, InOut(i, Values.Null), ResolveDirection.Upward), Final(Values.Bot)))
            } else if (unconditionalDereference) {
              // there is __some__ unconditional dereference, but parameter is not null
              handleNullContractEquation(Equation(Key(method, InOut(i, Values.Null), ResolveDirection.Upward), resultEquation.rhs))
            } else if (paramInfluence) {
              handleNullContractEquation(nullContractEquation(context, resultOrigins, i))
            } else {
              // no influence - result is the same as the main equation
              handleNullContractEquation(Equation(Key(method, InOut(i, Values.Null), ResolveDirection.Upward), resultEquation.rhs))
            }
            // ]]] null->... analysis

            // [[[ !null -> analysis
            if (paramInfluence) {
              handleNotNullContractEquation(notNullContractEquation(context, resultOrigins, i))
            } else {
              handleNotNullContractEquation(Equation(Key(method, InOut(i, Values.NotNull), ResolveDirection.Upward), resultEquation.rhs))
            }
          }
          // not leaking - approximating it by out equation
          else {
            handleNullContractEquation(Equation(Key(method, InOut(i, Values.Null), ResolveDirection.Upward), resultEquation.rhs))
            handleNotNullContractEquation(Equation(Key(method, InOut(i, Values.NotNull), ResolveDirection.Upward), resultEquation.rhs))
          }
        }
        // ]]] contract analysis
      }

    }
    val time = System.nanoTime() - start
    if (cycle) {
      cycleMethods += 1
      cycleTime += time
    } else {
      nonCycleMethods += 1
      nonCycleTime += time
    }
  }

  def buildCFG(className: String, methodNode: MethodNode, jsr: Boolean): ControlFlowGraph =
    controlFlow.buildControlFlowGraph(className, methodNode, jsr)

  def leakingParameters(className: String, methodNode: MethodNode, jsr: Boolean) =
    LeakingParameters.build(className, methodNode, jsr)

  // build other result origins
  def buildResultOrigins(className: String, methodNode: MethodNode, frames: Array[Frame[ParamsValue]], graph: ControlFlowGraph): Origins =
    OriginsAnalysis.resultOrigins(frames.asInstanceOf[Array[Frame[ASMValue]]], methodNode, graph)

  def buildDFSTree(transitions: Array[List[Int]]): DFSTree =
    controlFlow.buildDFSTree(transitions)

  def isReducible(graph: ControlFlowGraph, dfs: DFSTree): Boolean =
    controlFlow.reducible(graph, dfs)

  def purityEquation(method: Method, methodNode: MethodNode): Option[Equation[Key, Value]] =
    PurityAnalysis.analyze(method, methodNode)

  def notNullParamEquation(context: Context, i: Int): (Equation[Key, Value], Boolean) = {
    val analyser = new NotNullParameterAnalysis(context, In(i))
    try {
      val eq = analyser.analyze()
      (eq, analyser.npe)
    } catch {
      case _: LimitReachedException =>
        (Equation(analyser.aKey, Final(Values.Top)), analyser.npe)
    }
  }

  def nullableParamEquation(context: Context, i: Int): Equation[Key, Value] = {
    val analyser = new NullableParameterAnalysis(context, In(i))
    try {
      analyser.analyze()
    } catch {
      case _: LimitReachedException =>
        Equation(analyser.aKey, Final(Values.Top))
    }
  }

  def notNullContractEquation(context: Context, resultOrigins: Origins, i: Int): Equation[Key, Value] = {
    val analyser = new ResultAnalysis(context, InOut(i, Values.NotNull), resultOrigins)
    try {
      analyser.analyze()
    } catch {
      case _: LimitReachedException =>
        Equation(analyser.aKey, Final(Values.Top))
    }
  }

  def nullContractEquation(context: Context, resultOrigins: Origins, i: Int): Equation[Key, Value] = {
    val analyser = new ResultAnalysis(context, InOut(i, Values.Null), resultOrigins)
    try {
      analyser.analyze()
    } catch {
      case _: LimitReachedException =>
        Equation(analyser.aKey, Final(Values.Top))
    }
  }

  def outContractEquation(context: Context, resultOrigins: Origins): Equation[Key, Value] = {
    val analyser = new ResultAnalysis(context, Out, resultOrigins)
    try {
      analyser.analyze()
    } catch {
      case _: LimitReachedException =>
        Equation(analyser.aKey, Final(Values.Top))
    }
  }

  def nullableResultEquation(className: String, methodNode: MethodNode, method: Method, origins: Origins, jsr: Boolean): Equation[Key, Value] =
    Equation(Key(method, Out, ResolveDirection.Upward), NullableResultAnalysis.analyze(className, methodNode, origins.instructions, jsr))

  def handlePurityEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNotNullParamEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNullableParamEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNotNullContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNullContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleOutContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNullableResultEquation(eq: Equation[Key, Value]): Unit = ()

  /**
   *
   * @param classInfo class info available at index ("map") phase
   */
  def mapClassInfo(classInfo: ClassInfo) {}

  /**
   *
   * @param methodInfo method info available at index ("map") phase
   */
  def mapMethodInfo(methodInfo: MethodInfo) {}

}
