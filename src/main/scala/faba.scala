package faba

import faba.analysis.LimitReachedException
import faba.asm.nullableResult.NullableResultAnalysis
import faba.combined.{NegAnalysisFailure, NegAnalysis, CombinedSingleAnalysis}
import org.objectweb.asm._
import org.objectweb.asm.tree.{AbstractInsnNode, MethodNode}
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

    val method = Method(className, methodNode.name, methodNode.desc)
    val acc = methodNode.access
    val stable = stableClass || (methodNode.name == "<init>") ||
      (acc & ACC_FINAL) != 0 || (acc & ACC_PRIVATE) != 0 || (acc & ACC_STATIC) != 0

    if (!doNothing)
      extras = extras.updated(method, MethodExtra(Option(methodNode.signature), methodNode.access))

    handlePurityEquation(purityEquation(method, methodNode, stable))

    if (argumentTypes.length == 0 && !(isReferenceResult || isBooleanResult)) {
      return
    }


    if (!doNothing)
      extras = extras.updated(method, MethodExtra(Option(methodNode.signature), methodNode.access))

    var added = false
    val graph = buildCFG(className, methodNode, jsr)

    if (graph.transitions.nonEmpty) {
      val dfs = buildDFSTree(graph.transitions)
      val complex = dfs.back.nonEmpty || graph.transitions.exists(_.size > 1)

      // no jsr
      val start = System.nanoTime()
      if (complex) {
        val reducible = dfs.back.isEmpty || isReducible(graph, dfs)
        if (reducible) {
          val negated = tryNegation(method, argumentTypes, graph, isReferenceResult, isBooleanResult, stable, dfs, jsr);
          handleComplexMethod(method, className, methodNode, dfs, argumentTypes, graph, isReferenceResult, isBooleanResult, stable, jsr, negated)
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
        if (isReferenceArg && (isReferenceResult || isBooleanResult)) {
          handleNullContractEquation(Equation(Key(method, InOut(i, Values.Null), stable), Final(Values.Top)))
          handleNotNullContractEquation(Equation(Key(method, InOut(i, Values.NotNull), stable), Final(Values.Top)))
        }
      }
      if (isReferenceResult) {
        handleOutContractEquation(Equation(Key(method, Out, stable), Final(Values.Top)))
        handleNullableResultEquation(Equation(Key(method, Out, stable), Final(Values.Bot)))
      }
    }
  }

  def tryNegation(method: Method,
                  argumentTypes: Array[Type],
                  graph: ControlFlowGraph,
                  isReferenceResult: Boolean,
                  isBooleanResult: Boolean,
                  stable: Boolean,
                  dfs: DFSTree,
                  jsr: Boolean): Option[NegAnalysis]  = {

    def isMethodCall(opCode: Int): Boolean =
      opCode == Opcodes.INVOKESTATIC ||
        opCode == Opcodes.INVOKESPECIAL ||
        opCode == Opcodes.INVOKEVIRTUAL ||
        opCode == Opcodes.INVOKEINTERFACE

    val booleanConstInsns =
      Set(Opcodes.ICONST_0, Opcodes.ICONST_1)

    if (isBooleanResult && dfs.back.isEmpty && !jsr) {
      lazy val singleBranch =
        graph.transitions.count(_.size == 2) == 1

      lazy val singleIfInsn = {
        val insnIndex = graph.transitions.indexWhere(_.size == 2)
        val insn = graph.methodNode.instructions.get(insnIndex)
        val opCode = insn.getOpcode
        opCode == Opcodes.IFNE || opCode == Opcodes.IFEQ
      }

      lazy val singleMethodCall: Boolean = {
        graph.transitions.indices.count(i => isMethodCall(graph.methodNode.instructions.get(i).getOpcode)) == 1
      }

      lazy val booleanConstResult: Boolean = {
        lazy val leaking =
          leakingParameters(graph.className, graph.methodNode, jsr = false)
        val resultOrigins =
          buildResultOrigins(graph.className, graph.methodNode, leaking.frames, graph)
        val resultInsns: Set[Int] =
          resultOrigins.indices.filter(resultOrigins).map(i => graph.methodNode.instructions.get(i).getOpcode).toSet

        resultInsns == booleanConstInsns
      }

      if (singleBranch && singleIfInsn && singleMethodCall && booleanConstResult) {
        val analyzer = new NegAnalysis(method, graph)
        try {
          analyzer.analyze()
          return Some(analyzer)
        } catch {
          case NegAnalysisFailure =>
            return None
        }

      }

    }

    None
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
      handleNullableResultEquation(analyzer.nullableResultEquation(stable))
    }
    for (i <- argumentTypes.indices) {
      val argType = argumentTypes(i)
      val argSort = argType.getSort
      val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
      if (isReferenceArg) {
        handleNotNullParamEquation(analyzer.notNullParamEquation(i, stable))
        handleNullableParamEquation(analyzer.nullableParamEquation(i, stable))
      }
      if (isReferenceArg && (isReferenceResult || isBooleanResult)) {
        handleNullContractEquation(analyzer.contractEquation(i, Values.Null, stable))
        handleNotNullContractEquation(analyzer.contractEquation(i, Values.NotNull, stable))
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
                          jsr: Boolean,
                          negatedAnalysis: Option[NegAnalysis]) {
    val start = System.nanoTime()
    val cycle = dfs.back.nonEmpty
    // leaking params will be taken for
    lazy val leaking = leakingParameters(className, methodNode, jsr)

    lazy val resultOrigins = buildResultOrigins(className, methodNode, leaking.frames, graph)
    val richControlFlow = RichControlFlow(graph, dfs)
    lazy val resultEquation: Equation[Key, Value] = outContractEquation(richControlFlow, resultOrigins, stable)
    if (isReferenceResult) {
      handleOutContractEquation(resultEquation)
      handleNullableResultEquation(nullableResultEquation(className, methodNode, method, resultOrigins, stable, jsr))
    }
    for (i <- argumentTypes.indices) {
      val argType = argumentTypes(i)
      val argSort = argType.getSort
      val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
      val booleanArg = argType == Type.BOOLEAN_TYPE
      var notNullParam = false
      var touched = false
      if (isReferenceArg) {
        if (leaking.parameters(i)) {
          val (notNullPEquation, npe) = notNullParamEquation(richControlFlow, i, stable)
          touched = npe
          notNullParam = notNullPEquation.rhs == Final(Values.NotNull)
          handleNotNullParamEquation(notNullPEquation)
        }
        else
          handleNotNullParamEquation(Equation(Key(method, In(i), stable), Final(Values.Top)))

        if (leaking.nullableParameters(i)) {
          if (notNullParam || touched) // it was dereferenced
            handleNullableParamEquation(Equation(Key(method, In(i), stable), Final(Values.Top)))
          else
            handleNullableParamEquation(nullableParamEquation(richControlFlow, i, stable))
        }
        else
          handleNullableParamEquation(Equation(Key(method, In(i), stable), Final(Values.Null)))

      }
      if (isReferenceArg && (isReferenceResult || isBooleanResult)) {
        if (leaking.parameters(i)) {
          if (!notNullParam) {
            if (isBooleanResult && negatedAnalysis.isDefined) {
              handleNullContractEquation(negatedAnalysis.get.contractEquation(i, Values.Null, stable))
            } else {
              handleNullContractEquation(nullContractEquation(richControlFlow, resultOrigins, i, stable))
            }
          } else {
            handleNullContractEquation(Equation(Key(method, InOut(i, Values.Null), stable), Final(Values.Bot)))
          }
          if (isBooleanResult && negatedAnalysis.isDefined) {
            handleNotNullContractEquation(negatedAnalysis.get.contractEquation(i, Values.NotNull, stable))
          } else
            handleNotNullContractEquation(notNullContractEquation(richControlFlow, resultOrigins, i, stable))
        } else {
          handleNullContractEquation(Equation(Key(method, InOut(i, Values.Null), stable), resultEquation.rhs))
          handleNotNullContractEquation(Equation(Key(method, InOut(i, Values.NotNull), stable), resultEquation.rhs))
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

  def purityEquation(method: Method, methodNode: MethodNode, stable: Boolean): Equation[Key, Value] =
    PurityAnalysis.analyze(method, methodNode, stable)

  def notNullParamEquation(richControlFlow: RichControlFlow, i: Int, stable: Boolean): (Equation[Key, Value], Boolean) = {
    val analyser = new NotNullInAnalysis(richControlFlow, In(i), stable)
    try {
      val eq = analyser.analyze()
      (eq, analyser.npe)
    } catch {
      case _: LimitReachedException =>
        (Equation(analyser.aKey, Final(Values.Top)), analyser.npe)
    }
  }

  def nullableParamEquation(richControlFlow: RichControlFlow, i: Int, stable: Boolean): Equation[Key, Value] = {
    val analyser = new NullableInAnalysis(richControlFlow, In(i), stable)
    try {
      analyser.analyze()
    } catch {
      case _: LimitReachedException =>
        Equation(analyser.aKey, Final(Values.Top))
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

  def outContractEquation(richControlFlow: RichControlFlow, resultOrigins: Array[Boolean], stable: Boolean): Equation[Key, Value] = {
    val analyser = new InOutAnalysis(richControlFlow, Out, resultOrigins, stable)
    try {
      analyser.analyze()
    } catch {
      case _: LimitReachedException =>
        Equation(analyser.aKey, Final(Values.Top))
    }
  }

  def nullableResultEquation(className: String, methodNode: MethodNode, method: Method, origins: Array[Boolean], stable: Boolean, jsr: Boolean): Equation[Key, Value] =
    Equation(Key(method, Out, stable), NullableResultAnalysis.analyze(className, methodNode, origins, jsr))

  def handlePurityEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNotNullParamEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNullableParamEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNotNullContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNullContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleOutContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNullableResultEquation(eq: Equation[Key, Value]): Unit = ()

  def leakingParameters(className: String, methodNode: MethodNode, jsr: Boolean) =
    LeakingParameters.build(className, methodNode, jsr)
}
