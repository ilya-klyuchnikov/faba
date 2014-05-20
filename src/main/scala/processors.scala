package faba

import org.objectweb.asm.{MethodVisitor, Opcodes, ClassVisitor, ClassReader, Type}
import org.objectweb.asm.tree.MethodNode
import java.io.File

import faba.cfg._
import faba.data._
import faba.engine._
import faba.source._
import scala.xml.{PrettyPrinter}

object Main extends Processor {

  import faba.contracts._
  import faba.parameters._

  val solver = new Solver[AKey, Values.Value]()
  var extras = Map[Method, MethodExtra]()

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
    val method = Method(className, methodNode.name, methodNode.desc)
    extras = extras.updated(method, MethodExtra(Option(methodNode.signature), methodNode.access))

    val graph = cfg.buildControlFlowGraph(className, methodNode)

    var added = false
    val argumentTypes = Type.getArgumentTypes(methodNode.desc)
    val resultType = Type.getReturnType(methodNode.desc)
    val resultSort = resultType.getSort

    val isReferenceResult = resultSort == Type.OBJECT || resultSort == Type.ARRAY
    val isBooleanResult = Type.BOOLEAN_TYPE == resultType

    if (graph.transitions.nonEmpty)  {
      val dfs = cfg.buildDFSTree(graph.transitions)
      val reducible = dfs.back.isEmpty || cfg.reducible(graph, dfs)
      if (reducible) {
        for (i <- argumentTypes.indices) {
          val argType = argumentTypes(i)
          val sort = argType.getSort
          if (sort == Type.OBJECT || sort == Type.ARRAY) {
            solver.addEquation(new NotNullInAnalysis(RichControlFlow(graph, dfs), i).analyze())
          }
          if (isReferenceResult || isBooleanResult) {
            if (sort == Type.OBJECT || sort == Type.ARRAY) {
              solver.addEquation(new InOutAnalysis(RichControlFlow(graph, dfs), InOut(i, Values.Null)).analyze())
              solver.addEquation(new InOutAnalysis(RichControlFlow(graph, dfs), InOut(i, Values.NotNull)).analyze())
            }
            if (argType == Type.BOOLEAN_TYPE) {
              solver.addEquation(new InOutAnalysis(RichControlFlow(graph, dfs), InOut(i, Values.False)).analyze())
              solver.addEquation(new InOutAnalysis(RichControlFlow(graph, dfs), InOut(i, Values.True)).analyze())
            }
          }
        }
        if (isReferenceResult) {
          solver.addEquation(new InOutAnalysis(RichControlFlow(graph, dfs), Out).analyze())
        }
        added = true
      } else {
        println(s"Warning: CFG for $className ${methodNode.name}${methodNode.desc} is not reducible. Skipped")
      }
    }

    if (!added) {
      val method = Method(className, methodNode.name, methodNode.desc)
      for (i <- argumentTypes.indices) {
        val argType: Type = argumentTypes(i)
        val sort = argType.getSort
        if (sort == Type.OBJECT || sort == Type.ARRAY) {
          solver.addEquation(Equation(AKey(method, InOut(i, Values.Null)), Final(Values.Top)))
          solver.addEquation(Equation(AKey(method, InOut(i, Values.NotNull)), Final(Values.Top)))
          solver.addEquation(Equation(AKey(method, In(i)), Final(Values.Top)))
        }
        if (argType == Type.BOOLEAN_TYPE) {
          solver.addEquation(Equation(AKey(method, InOut(i, Values.False)), Final(Values.Top)))
          solver.addEquation(Equation(AKey(method, InOut(i, Values.True)), Final(Values.Top)))
        }
      }
      if (isReferenceResult) {
        solver.addEquation(Equation(AKey(method, Out), Final(Values.Top)))
      }
    }
  }

  def printToFile(f: java.io.File)(op: java.io.PrintWriter => Unit) {
    f.getParentFile.mkdirs()
    val p = new java.io.PrintWriter(f)
    try { op(p) } finally { p.close() }
  }

  def process(source: Source, outDir: String) {
    val pp = new PrettyPrinter(1000, 2)
    val sep = File.separatorChar
    val indexStart = System.currentTimeMillis()
    println("indexing ...")
    source.process(this)
    val indexEnd = System.currentTimeMillis()

    println("solving ...")
    val solutions: Map[AKey, Values.Value] =
      solver.solve().filterNot(p => p._2 == Values.Top || p._2 == Values.Bot)
    val solvingEnd = System.currentTimeMillis()
    println("saving to file ...")

    val byPackage: Map[String, Map[AKey, Values.Value]] =
      solutions.groupBy(_._1.method.internalPackageName)

    for ((pkg, solution) <- byPackage) {
      val xmlAnnotations = XmlUtils.toXmlAnnotations(solution, extras)
      printToFile(new File(s"${outDir}${sep}${pkg.replace('/', sep)}${sep}annotations.xml")) { out =>
        out.println(pp.format(<root>{xmlAnnotations}</root>))
      }

    }

    val writingEnd = System.currentTimeMillis()

    println("====")
    println(s"indexing took ${(indexEnd - indexStart) / 1000.0} sec")
    println(s"solving took ${(solvingEnd - indexEnd) / 1000.0} sec")
    println(s"saving took ${(writingEnd - solvingEnd) / 1000.0} sec")

    println(s"${solutions.size} contracts")
  }

  def main(args: Array[String]) {
    if (args.length != 2) {
      println(s"Usage: faba.Main inputJar outputDir")
    } else {
      process(JarFileSource(new File(args(0))), args(1))
    }
  }

}
