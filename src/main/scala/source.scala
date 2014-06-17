package faba.source

import org.objectweb.asm._
import org.objectweb.asm.tree.MethodNode

import scala.language.existentials
import scala.collection.JavaConverters._

import java.io.File
import java.util.jar.JarFile

import faba.cfg
import faba.cfg._
import faba.contracts._
import faba.data._
import faba.engine._
import faba.parameters._

sealed trait Source {
  def process(processor: Processor): Unit
}

case class ClassSource(classes: Class[_]*) extends Source {
  override def process(processor: Processor): Unit =
    classes.foreach { clazz =>
      processor.processClass(new ClassReader(clazz.getCanonicalName))
    }
}

case class JarFileSource(file: File) extends Source {
  override def process(processor: Processor): Unit = {
    val jarFile = new JarFile(file)
    for (entry <- jarFile.entries().asScala) {
      if (entry.getName.endsWith(".class")) {
        val is = jarFile.getInputStream(entry)
        try {
          processor.processClass(new ClassReader(is))
        } finally {
          is.close()
        }
      }
    }
  }
}

case class MixedSource(sources: List[Source]) extends Source {
  override def process(processor: Processor): Unit =
    sources.foreach(_.process(processor))
}

trait Processor {
  def processClass(classReader: ClassReader): Unit
}

/** default faba processor */
trait FabaProcessor extends Processor {
  val paramsSolver = new Solver[Key, Values.Value]()(ELattice(Values.NotNull, Values.Top))
  val contractsSolver = new Solver[Key, Values.Value]()(ELattice(Values.Bot, Values.Top))
  val processContracts = true
  var extras = Map[Method, MethodExtra]()

  override def processClass(classReader: ClassReader): Unit =
    classReader.accept(new ClassVisitor(Opcodes.ASM5) {
      var stableClass = false
      override def visit(version: Int, access: Int, name: String, signature: String, superName: String, interfaces: Array[String]) {
        // or there are no subclasses??
        stableClass = (access & Opcodes.ACC_FINAL) != 0
        super.visit(version, access, name, signature, superName, interfaces)
      }

      override def visitMethod(access: Int, name: String, desc: String, signature: String, exceptions: Array[String]) = {
        val node = new MethodNode(Opcodes.ASM5, access, name, desc, signature, exceptions)
        new MethodVisitor(Opcodes.ASM5, node) {
          override def visitEnd(): Unit = {
            super.visitEnd()
            processMethod(classReader.getClassName, node, stableClass)
          }
        }
      }
    }, 0)

  def processMethod(className: String, methodNode: MethodNode, stableClass: Boolean) {
    val method = Method(className, methodNode.name, methodNode.desc)
    extras = extras.updated(method, MethodExtra(Option(methodNode.signature), methodNode.access))
    val access = methodNode.access
    val stable =
      stableClass ||
        (access & Opcodes.ACC_FINAL) != 0 ||
        (access & Opcodes.ACC_PRIVATE) != 0 ||
        (access & Opcodes.ACC_STATIC) != 0 ||
        (methodNode.name == "<init>")

    val graph = buildCFG(className, methodNode)
    var added = false
    val argumentTypes = Type.getArgumentTypes(methodNode.desc)
    val resultType = Type.getReturnType(methodNode.desc)
    val resultSort = resultType.getSort

    val isReferenceResult = resultSort == Type.OBJECT || resultSort == Type.ARRAY
    val isBooleanResult = Type.BOOLEAN_TYPE == resultType

    if (graph.transitions.nonEmpty)  {
      val dfs = buildDFSTree(graph.transitions)
      val reducible = dfs.back.isEmpty || isReducible(graph, dfs)
      if (reducible) {
        val resultOrigins: Set[Int] = buildResultOrigins(className, methodNode)
        for (i <- argumentTypes.indices) {
          val argType = argumentTypes(i)
          val argSort = argType.getSort
          val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
          val booleanArg = argType == Type.BOOLEAN_TYPE
          if (isReferenceArg) {
            paramsSolver.addEquation(notNullParamEquation(RichControlFlow(graph, dfs), i, stable))
          }
          if (processContracts && isReferenceArg && (isReferenceResult || isBooleanResult)) {
            contractsSolver.addEquation(nullContractEquation(RichControlFlow(graph, dfs), resultOrigins, i, stable))
            contractsSolver.addEquation(notNullContractEquation(RichControlFlow(graph, dfs), resultOrigins, i, stable))
          }
          if (processContracts && booleanArg && (isReferenceResult || isBooleanResult)) {
            contractsSolver.addEquation(falseContractEquation(RichControlFlow(graph, dfs), resultOrigins, i, stable))
            contractsSolver.addEquation(trueContractEquation(RichControlFlow(graph, dfs), resultOrigins, i, stable))
          }
        }
        if (processContracts && isReferenceResult) {
          contractsSolver.addEquation(outContractEquation(RichControlFlow(graph, dfs), resultOrigins, stable))
        }
        added = true
      } else {
        println(s"Warning: CFG for $className ${methodNode.name}${methodNode.desc} is not reducible. Skipped")
      }
    }

    if (!added) {
      for (i <- argumentTypes.indices) {
        val argType = argumentTypes(i)
        val argSort = argType.getSort
        val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
        val booleanArg = argType == Type.BOOLEAN_TYPE
        if (isReferenceArg) {
          paramsSolver.addEquation(Equation(Key(method, In(i), stable), Final(Values.Top)))
        }
        if (processContracts && isReferenceArg && (isReferenceResult || isBooleanResult)) {
          contractsSolver.addEquation(Equation(Key(method, InOut(i, Values.Null), stable), Final(Values.Top)))
          contractsSolver.addEquation(Equation(Key(method, InOut(i, Values.NotNull), stable), Final(Values.Top)))
        }
        if (processContracts && booleanArg && (isReferenceResult || isBooleanResult)) {
          contractsSolver.addEquation(Equation(Key(method, InOut(i, Values.True), stable), Final(Values.Top)))
          contractsSolver.addEquation(Equation(Key(method, InOut(i, Values.False), stable), Final(Values.Top)))
        }
      }
      if (processContracts && isReferenceResult) {
        contractsSolver.addEquation(Equation(Key(method, Out, stable), Final(Values.Top)))
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

  def notNullParamEquation(richControlFlow: RichControlFlow, i: Int, stable: Boolean) =
    new NotNullInAnalysis(richControlFlow, In(i), stable).analyze()

  def notNullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int, stable: Boolean) =
    new InOutAnalysis(richControlFlow, InOut(i, Values.NotNull), resultOrigins, stable).analyze()

  def nullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int, stable: Boolean) =
    new InOutAnalysis(richControlFlow, InOut(i, Values.Null), resultOrigins, stable).analyze()

  def trueContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int, stable: Boolean) =
    new InOutAnalysis(richControlFlow, InOut(i, Values.True), resultOrigins, stable).analyze()

  def falseContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int, stable: Boolean) =
    new InOutAnalysis(richControlFlow, InOut(i, Values.False), resultOrigins, stable).analyze()

  def outContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], stable: Boolean) =
    new InOutAnalysis(richControlFlow, Out, resultOrigins, stable).analyze()
}
