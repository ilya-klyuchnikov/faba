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
  val solver = new Solver[Key, Values.Value]()
  val processContracts = true

  override def processClass(classReader: ClassReader): Unit =
    classReader.accept(new ClassVisitor(Opcodes.ASM5) {
      override def visitMethod(access: Int, name: String, desc: String, signature: String, exceptions: Array[String]) = {
        val node = new MethodNode(Opcodes.ASM5, access, name, desc, signature, exceptions)
        new MethodVisitor(Opcodes.ASM5, node) {
          override def visitEnd(): Unit = {
            super.visitEnd()
            processMethod(classReader.getClassName, node)
          }
        }
      }
    }, 0)

  def processMethod(className: String, methodNode: MethodNode) {

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
            solver.addEquation(notNullParamEquation(RichControlFlow(graph, dfs), i))
          }
          if (processContracts && isReferenceArg && (isReferenceResult || isBooleanResult)) {
            solver.addEquation(nullContractEquation(RichControlFlow(graph, dfs), resultOrigins, i))
            solver.addEquation(notNullContractEquation(RichControlFlow(graph, dfs), resultOrigins, i))
          }
          if (processContracts && booleanArg && (isReferenceResult || isBooleanResult)) {
            solver.addEquation(falseContractEquation(RichControlFlow(graph, dfs), resultOrigins, i))
            solver.addEquation(trueContractEquation(RichControlFlow(graph, dfs), resultOrigins, i))
          }
        }
        if (processContracts && isReferenceResult) {
          solver.addEquation(outContractEquation(RichControlFlow(graph, dfs), resultOrigins))
        }
        added = true
      } else {
        println(s"Warning: CFG for $className ${methodNode.name}${methodNode.desc} is not reducible. Skipped")
      }
    }

    if (!added) {
      val method = Method(className, methodNode.name, methodNode.desc)
      for (i <- argumentTypes.indices) {
        val argType = argumentTypes(i)
        val argSort = argType.getSort
        val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
        val booleanArg = argType == Type.BOOLEAN_TYPE
        if (isReferenceArg) {
          solver.addEquation(Equation(Key(method, In(i)), Final(Values.Top)))
        }
        if (processContracts && isReferenceArg && (isReferenceResult || isBooleanResult)) {
          solver.addEquation(Equation(Key(method, InOut(i, Values.Null)), Final(Values.Top)))
          solver.addEquation(Equation(Key(method, InOut(i, Values.NotNull)), Final(Values.Top)))
        }
        if (processContracts && booleanArg && (isReferenceResult || isBooleanResult)) {
          solver.addEquation(Equation(Key(method, InOut(i, Values.True)), Final(Values.Top)))
          solver.addEquation(Equation(Key(method, InOut(i, Values.False)), Final(Values.Top)))
        }
      }
      if (processContracts && isReferenceResult) {
        solver.addEquation(Equation(Key(method, Out), Final(Values.Top)))
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

  def notNullParamEquation(richControlFlow: RichControlFlow, i: Int) =
    new NotNullInAnalysis(richControlFlow, In(i)).analyze()

  def notNullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int) =
    new InOutAnalysis(richControlFlow, InOut(i, Values.NotNull), resultOrigins).analyze()

  def nullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int) =
    new InOutAnalysis(richControlFlow, InOut(i, Values.Null), resultOrigins).analyze()

  def trueContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int) =
    new InOutAnalysis(richControlFlow, InOut(i, Values.True), resultOrigins).analyze()

  def falseContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int) =
    new InOutAnalysis(richControlFlow, InOut(i, Values.False), resultOrigins).analyze()

  def outContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int]) =
    new InOutAnalysis(richControlFlow, Out, resultOrigins).analyze()
}
