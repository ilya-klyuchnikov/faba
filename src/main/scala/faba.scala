package faba

import org.objectweb.asm._
import org.objectweb.asm.tree.MethodNode
import org.objectweb.asm.Opcodes._

import scala.language.existentials

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

  val processContracts = true
  var extras = Map[Method, MethodExtra]()

  def handleHierarchy(access: Int, thisName: String, superName: String) {

  }

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
          override def visitEnd(): Unit = {
            super.visitEnd()
            processMethod(classReader.getClassName, node, stableClass)
          }
        }
      }
    }, ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES)

  def processMethod(className: String, methodNode: MethodNode, stableClass: Boolean) {
    val argumentTypes = Type.getArgumentTypes(methodNode.desc)
    val resultType = Type.getReturnType(methodNode.desc)
    val resultSort = resultType.getSort

    val isReferenceResult = resultSort == Type.OBJECT || resultSort == Type.ARRAY
    val isBooleanResult = Type.BOOLEAN_TYPE == resultType

    if (argumentTypes.length == 0 && !(isReferenceResult || isBooleanResult)) {
      return
    }

    val method = Method(className, methodNode.name, methodNode.desc)
    extras = extras.updated(method, MethodExtra(Option(methodNode.signature), methodNode.access))
    val acc = methodNode.access
    val stable = stableClass || (methodNode.name == "<init>") ||
      (acc & ACC_FINAL) != 0 || (acc & ACC_PRIVATE) != 0 || (acc & ACC_STATIC) != 0

    val graph = buildCFG(className, methodNode)
    var added = false
    if (graph.transitions.nonEmpty)  {
      val dfs = buildDFSTree(graph.transitions)
      val reducible = dfs.back.isEmpty || isReducible(graph, dfs)
      if (reducible) {
        lazy val (leaking, nullableLeaking) = leakingParameters(className, methodNode)
        lazy val resultOrigins: Set[Int] = buildResultOrigins(className, methodNode)
        lazy val resultEquation: Equation[Key, Value] = outContractEquation(RichControlFlow(graph, dfs), resultOrigins, stable)
        if (processContracts && isReferenceResult) {
          handleOutContractEquation(resultEquation)
        }
        for (i <- argumentTypes.indices) {
          val argType = argumentTypes(i)
          val argSort = argType.getSort
          val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
          val booleanArg = argType == Type.BOOLEAN_TYPE
          if (isReferenceArg) {
            if (leaking(i))
              handleNotNullParamEquation(notNullParamEquation(RichControlFlow(graph, dfs), i, stable))
            else
              handleNotNullParamEquation(Equation(Key(method, In(i), stable), Final(Values.Top)))

            if (nullableLeaking(i))
              handleNullableParamEquation(nullableParamEquation(RichControlFlow(graph, dfs), i, stable))
            else
              handleNullableParamEquation(Equation(Key(method, In(i), stable), Final(Values.Null)))

          }
          if (processContracts && isReferenceArg && (isReferenceResult || isBooleanResult)) {
            if (leaking(i)) {
              handleNullContractEquation(nullContractEquation(RichControlFlow(graph, dfs), resultOrigins, i, stable))
              handleNotNullContractEquation(notNullContractEquation(RichControlFlow(graph, dfs), resultOrigins, i, stable))
            } else {
              handleNullContractEquation(Equation(Key(method, InOut(i, Values.Null), stable), resultEquation.rhs))
              handleNotNullContractEquation(Equation(Key(method, InOut(i, Values.NotNull), stable), resultEquation.rhs))
            }
          }
          if (processContracts && booleanArg && (isReferenceResult || isBooleanResult)) {
            if (leaking(i)) {
              handleFalseContractEquation(falseContractEquation(RichControlFlow(graph, dfs), resultOrigins, i, stable))
              handleTrueContractEquation(trueContractEquation(RichControlFlow(graph, dfs), resultOrigins, i, stable))
            } else {
              handleTrueContractEquation(Equation(Key(method, InOut(i, Values.True), stable), resultEquation.rhs))
              handleFalseContractEquation(Equation(Key(method, InOut(i, Values.False), stable), resultEquation.rhs))
            }
          }
        }

        added = true
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

  def buildCFG(className: String, methodNode: MethodNode): ControlFlowGraph =
    cfg.buildControlFlowGraph(className, methodNode)

  def buildResultOrigins(className: String, methodNode: MethodNode): Set[Int] =
    cfg.resultOrigins(className, methodNode)

  def buildDFSTree(transitions: Array[List[Int]]): DFSTree =
    cfg.buildDFSTree(transitions)

  def isReducible(graph: ControlFlowGraph, dfs: DFSTree): Boolean =
    cfg.reducible(graph, dfs)

  def notNullParamEquation(richControlFlow: RichControlFlow, i: Int, stable: Boolean): Equation[Key, Value] =
    new NotNullInAnalysis(richControlFlow, In(i), stable).analyze()

  def nullableParamEquation(richControlFlow: RichControlFlow, i: Int, stable: Boolean): Equation[Key, Value] =
    new NullableInAnalysis(richControlFlow, In(i), stable).analyze()

  def notNullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int, stable: Boolean): Equation[Key, Value] =
    new InOutAnalysis(richControlFlow, InOut(i, Values.NotNull), resultOrigins, stable).analyze()

  def nullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int, stable: Boolean): Equation[Key, Value] =
    new InOutAnalysis(richControlFlow, InOut(i, Values.Null), resultOrigins, stable).analyze()

  def trueContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int, stable: Boolean): Equation[Key, Value] =
    new InOutAnalysis(richControlFlow, InOut(i, Values.True), resultOrigins, stable).analyze()

  def falseContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int, stable: Boolean): Equation[Key, Value] =
    new InOutAnalysis(richControlFlow, InOut(i, Values.False), resultOrigins, stable).analyze()

  def outContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], stable: Boolean): Equation[Key, Value] =
    new InOutAnalysis(richControlFlow, Out, resultOrigins, stable).analyze()

  def handleNotNullParamEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNullableParamEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNotNullContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleNullContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleTrueContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleFalseContractEquation(eq: Equation[Key, Value]): Unit = ()
  def handleOutContractEquation(eq: Equation[Key, Value]): Unit = ()

  def leakingParameters(className: String, methodNode: MethodNode): (Set[Int], Set[Int]) =
    cfg.leakingParameters(className, methodNode)
}
