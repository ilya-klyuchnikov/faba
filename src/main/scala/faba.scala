package faba

import faba.analysis.LimitReachedException
import faba.combined.CombinedSingleAnalysis
import org.objectweb.asm._
import org.objectweb.asm.tree.MethodNode
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.analysis.Frame

import scala.language.existentials

import faba.asm._
import faba.cfg._
import faba.data._
import faba.contracts._
import faba.parameters._
import faba.engine._
import faba.source._

/**
 * Default faba processor. A lot of fine-grained method to override.
 **/
trait FabaProcessor extends Processor {
  val doNothing = false
  val processContracts = true
  var extras = Map[Method, MethodExtra]()
  var complexTime: Long = 0
  var nonCycleTime: Long = 0
  var cycleTime: Long = 0
  var nonCycleMethods: Long = 0
  var cycleMethods: Long = 0
  var simpleTime: Long = 0
  var complexMethods: Long = 0
  var simpleMethods: Long = 0

  def handleHierarchy(access: Int, thisName: String, superName: String) {}

  override def processClass(classReader: ClassReader): Unit =
    classReader.accept(new ClassVisitor(ASM5) {
      var stableClass = false
      override def visit(version: Int, access: Int, name: String, signature: String, superName: String, interfaces: Array[String]) {
        // or there are no subclasses??
        stableClass = (access & ACC_FINAL) != 0
        super.visit(version, access, name, signature, superName, interfaces)
        handleHierarchy(access, classReader.getClassName, superName)
      }

      override def visitMethod(access: Int, name: String, desc: String, signature: String, exceptions: Array[String]) = {
        val node = new MethodNode(ASM5, access, name, desc, signature, exceptions)
        new MethodVisitor(ASM5, node) {
          var jsr = false
          override def visitEnd(): Unit = {
            super.visitEnd()
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

    if (argumentTypes.length == 0 && !(isReferenceResult || isBooleanResult)) {
      return
    }

    val method = Method(className, methodNode.name, methodNode.desc)
    if (!doNothing)
      extras = extras.updated(method, MethodExtra(Option(methodNode.signature), methodNode.access))

    val acc = methodNode.access
    val stable = stableClass || (methodNode.name == "<init>") ||
      (acc & ACC_FINAL) != 0 || (acc & ACC_PRIVATE) != 0 || (acc & ACC_STATIC) != 0
    var added = false


    val graph = buildCFG(className, methodNode, jsr)
    if (graph.transitions.nonEmpty) {
      val dfs = buildDFSTree(graph.transitions)
      val complex = dfs.back.nonEmpty || graph.transitions.exists(_.size > 1)
      val start = System.nanoTime()
      if (complex) {
        val reducible = dfs.back.isEmpty || isReducible(graph, dfs)
        if (reducible) {
          handleComplexMethod(method, className, methodNode, dfs, argumentTypes, graph, isReferenceResult, isBooleanResult, stable, jsr)
          added = true
        }
      } else {
        handleSimpleMethod(method, argumentTypes, graph, isReferenceResult, isBooleanResult, stable)
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
        val booleanArg = argType == Type.BOOLEAN_TYPE
        if (isReferenceArg) {
          handleNotNullParamEquation(Equation(Key(method, In(i), stable), Final(Values.Top)))
        }
        if (processContracts && isReferenceArg && (isReferenceResult || isBooleanResult)) {
          handleNullContractEquation(Equation(Key(method, InOut(i, Values.Null), stable), Final(Values.Top)))
          handleNotNullContractEquation(Equation(Key(method, InOut(i, Values.NotNull), stable), Final(Values.Top)))
        }
        if (processContracts && booleanArg && (isReferenceResult || isBooleanResult)) {
          handleTrueContractEquation(Equation(Key(method, InOut(i, Values.True), stable), Final(Values.Top)))
          handleFalseContractEquation(Equation(Key(method, InOut(i, Values.False), stable), Final(Values.Top)))
        }
      }
      if (processContracts && isReferenceResult) {
        handleOutContractEquation(Equation(Key(method, Out, stable), Final(Values.Top)))
      }
    }
  }

  def handleSimpleMethod(method: Method,
                         argumentTypes: Array[Type],
                         graph: ControlFlowGraph,
                         isReferenceResult: Boolean,
                         isBooleanResult: Boolean,
                         stable: Boolean) {
    val analyzer = new CombinedSingleAnalysis(method, graph)
    analyzer.analyze()
    // todo - boolean result as well
    if (isReferenceResult) {
      handleOutContractEquation(analyzer.outContractEquation(stable))
    }
    for (i <- argumentTypes.indices) {
      val argType = argumentTypes(i)
      val argSort = argType.getSort
      val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
      val booleanArg = argType == Type.BOOLEAN_TYPE
      if (isReferenceArg) {
        handleNotNullParamEquation(analyzer.notNullParamEquation(i, stable))
        handleNullableParamEquation(analyzer.nullableParamEquation(i, stable))
      }
      if (isReferenceArg && (isReferenceResult || isBooleanResult)) {
        handleNullContractEquation(analyzer.nullContractEquation(i, stable))
        handleNotNullContractEquation(analyzer.notNullContractEquation(i, stable))
      }
      if (booleanArg && (isReferenceResult || isBooleanResult)) {
        handleFalseContractEquation(analyzer.falseContractEquation(i, stable))
        handleTrueContractEquation(analyzer.trueContractEquation(i, stable))
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
                          stable: Boolean,
                          jsr: Boolean) {
    val start = System.nanoTime()
    val cycle = dfs.back.nonEmpty
    // leaking params will be taken for
    lazy val leaking = leakingParameters(className, methodNode, jsr)

    lazy val resultOrigins = buildResultOrigins(className, methodNode, leaking.frames, graph)
    val richControlFlow = RichControlFlow(graph, dfs)
    lazy val resultEquation: Equation[Key, Value] = outContractEquation(richControlFlow, resultOrigins, stable)
    if (processContracts && isReferenceResult) {
      handleOutContractEquation(resultEquation)
    }
    for (i <- argumentTypes.indices) {
      val argType = argumentTypes(i)
      val argSort = argType.getSort
      val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
      val booleanArg = argType == Type.BOOLEAN_TYPE
      var notNullParam = false
      if (isReferenceArg) {
        if (leaking.nullableParameters(i)) {
          val (notNullEquation, nullableEquation) = paramEquations(richControlFlow, i, stable)
          notNullParam = notNullEquation.rhs == Final(Values.NotNull)
          handleNotNullParamEquation(notNullEquation)
          handleNullableParamEquation(nullableEquation)
        }
        else {
          handleNotNullParamEquation(Equation(Key(method, In(i), stable), Final(Values.Top)))
          handleNullableParamEquation(Equation(Key(method, In(i), stable), Final(Values.Null)))
        }
      }
      if (processContracts && isReferenceArg && (isReferenceResult || isBooleanResult)) {
        if (leaking.parameters(i)) {
          if (!notNullParam) {
            handleNullContractEquation(nullContractEquation(richControlFlow, resultOrigins, i, stable))
          } else {
            handleNullContractEquation(Equation(Key(method, InOut(i, Values.Null), stable), Final(Values.Bot)))
          }
          handleNotNullContractEquation(notNullContractEquation(richControlFlow, resultOrigins, i, stable))
        } else {
          handleNullContractEquation(Equation(Key(method, InOut(i, Values.Null), stable), resultEquation.rhs))
          handleNotNullContractEquation(Equation(Key(method, InOut(i, Values.NotNull), stable), resultEquation.rhs))
        }
      }
      if (processContracts && booleanArg && (isReferenceResult || isBooleanResult)) {
        if (leaking.parameters(i)) {
          handleFalseContractEquation(falseContractEquation(richControlFlow, resultOrigins, i, stable))
          handleTrueContractEquation(trueContractEquation(richControlFlow, resultOrigins, i, stable))
        } else {
          handleTrueContractEquation(Equation(Key(method, InOut(i, Values.True), stable), resultEquation.rhs))
          handleFalseContractEquation(Equation(Key(method, InOut(i, Values.False), stable), resultEquation.rhs))
        }
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
    cfg.buildControlFlowGraph(className, methodNode, jsr)

  private def isReturnOpcode(opcode: Int) =
    opcode >= Opcodes.IRETURN && opcode <= Opcodes.ARETURN

  // build other result origins
  def buildResultOrigins(className: String, methodNode: MethodNode, frames: Array[Frame[ParamsValue]], graph: ControlFlowGraph): Array[Boolean] = {
    val insns = methodNode.instructions
    val returnIndices = (0 until frames.length).filter { i => isReturnOpcode(insns.get(i).getOpcode)}.toList
    OriginsAnalysis.resultOrigins(frames, insns, graph, returnIndices)
  }

  def buildDFSTree(transitions: Array[List[Int]]): DFSTree =
    cfg.buildDFSTree(transitions)

  def isReducible(graph: ControlFlowGraph, dfs: DFSTree): Boolean =
    cfg.reducible(graph, dfs)

  // @NotNull, @Nullable
  def paramEquations(richControlFlow: RichControlFlow, i: Int, stable: Boolean): (Equation[Key, Value], Equation[Key, Value]) = {
    val analyser = new NullityInAnalysis(richControlFlow, In(i), stable)
    try {
      analyser.analyze()
      (analyser.mkNotNullEquation, analyser.mkNullableEquation)
    } catch {
      case _: LimitReachedException =>
        (Equation(analyser.aKey, Final(Values.Top)), Equation(analyser.aKey, Final(Values.Top)))
    }
  }

  def notNullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Array[Boolean], i: Int, stable: Boolean): Equation[Key, Value] = {
    val analyser = new InOutAnalysis(richControlFlow, InOut(i, Values.NotNull), resultOrigins, stable)
    try {
      analyser.analyze()
    } catch {
      case _: LimitReachedException =>
        Equation(analyser.aKey, Final(Values.Top))
    }
  }

  def nullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Array[Boolean], i: Int, stable: Boolean): Equation[Key, Value] = {
    val analyser = new InOutAnalysis(richControlFlow, InOut(i, Values.Null), resultOrigins, stable)
    try {
      analyser.analyze()
    } catch {
      case _: LimitReachedException =>
        Equation(analyser.aKey, Final(Values.Top))
    }
  }

  def trueContractEquation(richControlFlow: RichControlFlow, resultOrigins: Array[Boolean], i: Int, stable: Boolean): Equation[Key, Value] = {
    val analyser = new InOutAnalysis(richControlFlow, InOut(i, Values.True), resultOrigins, stable)
    try {
      analyser.analyze()
    } catch {
      case _: LimitReachedException =>
        Equation(analyser.aKey, Final(Values.Top))
    }
  }

  def falseContractEquation(richControlFlow: RichControlFlow, resultOrigins: Array[Boolean], i: Int, stable: Boolean): Equation[Key, Value] = {
    val analyser = new InOutAnalysis(richControlFlow, InOut(i, Values.False), resultOrigins, stable)
    try {
      analyser.analyze()
    } catch {
      case _: LimitReachedException =>
        Equation(analyser.aKey, Final(Values.Top))
    }
  }

  def outContractEquation(richControlFlow: RichControlFlow, resultOrigins: Array[Boolean], stable: Boolean): Equation[Key, Value] = {
    val analyser = new InOutAnalysis(richControlFlow, Out, resultOrigins, stable)
    try {
      analyser.analyze()
    } catch {
      case _: LimitReachedException =>
        Equation(analyser.aKey, Final(Values.Top))
    }
  }

  def handleNotNullParamEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNullableParamEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNotNullContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNullContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleTrueContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleFalseContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleOutContractEquation(eq: Equation[Key, Value]): Unit = ()

  def leakingParameters(className: String, methodNode: MethodNode, jsr: Boolean) =
    LeakingParameters.build(className, methodNode, jsr)
}
