package faba

import org.objectweb.asm.{MethodVisitor, Opcodes, ClassVisitor, ClassReader, Type}
import org.objectweb.asm.tree.MethodNode
import java.io.File
import scala.collection.mutable.ArrayBuffer

import faba.cfg._
import faba.data._
import faba.engine._
import faba.source._

@deprecated
object NotNullParametersProcessor extends Processor {

  import faba.parameters._
  val solver = new Solver[Id, Value]()

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
    val graph = cfg.buildControlFlowGraph(className, methodNode)
    var added = false
    val argumentTypes = Type.getArgumentTypes(methodNode.desc)
    if (graph.transitions.nonEmpty)  {
      val dfs = cfg.buildDFSTree(graph.transitions)
      val reducible = dfs.back.isEmpty || cfg.reducible(graph, dfs)
      if (reducible) {
        for (i <- argumentTypes.indices) {
          val sort = argumentTypes(i).getSort
          if (sort == Type.OBJECT || sort == Type.ARRAY) {
            val equation = new NotNullInAnalysis(RichControlFlow(graph, dfs), i).analyze()
            solver.addEquation(equation)
          }
        }
        added = true
      } else {
        println(s"Warning: CFG for $className ${methodNode.name}${methodNode.desc} is not reducible. Skipped")
      }
    }

    if (!added) {
      val method = Method(className, methodNode.name, methodNode.desc)
      for (i <- argumentTypes.indices) {
        val sort = argumentTypes(i).getSort
        if (sort == Type.OBJECT || sort == Type.ARRAY) {
          solver.addEquation(Equation(AKey(method, In(i)), Final(Nullity.Nullable)))
        }
      }
    }
  }

  def printToFile(f: java.io.File)(op: java.io.PrintWriter => Unit) {
    val p = new java.io.PrintWriter(f)
    try { op(p) } finally { p.close() }
  }


  def process(source: Source, outFile: String) {
    val indexStart = System.currentTimeMillis()
    println("indexing ...")
    source.process(this)
    val indexEnd = System.currentTimeMillis()
    println("solving ...")
    val solutions = solver.solve().filter(_._2 == Nullity.NotNull)
    val solvingEnd = System.currentTimeMillis()
    println("saving to file ...")

    val outs = ArrayBuffer[String]()
    for ((parameter, v) <- solutions) {
      outs.append(parameter.toString.replace('/', '.'))
    }

    val outsSorted = outs.sorted
    printToFile(new File(outFile)) { out =>
      for (parameter <- outsSorted) {
        out.println(parameter)
      }
    }
    val writingEnd = System.currentTimeMillis()

    println("====")
    println(s"indexing took ${(indexEnd - indexStart)/1000.0} sec")
    println(s"solving took ${(solvingEnd - indexEnd)/1000.0} sec")
    println(s"saving took ${(writingEnd - solvingEnd)/1000.0} sec")
  }

  def main(args: Array[String]) {
    if (args.length != 2) {
      println(s"Usage: faba.NullBooleanContractsProcessor inputJar outputFile")
    } else {
      process(JarFileSource(new File(args(0))), args(1))
    }
  }

}

object Main extends Processor {

  import faba.contracts._
  import faba.parameters._

  val outSolver = new Solver[AKey, Values.Value]()
  val inSolver = new Solver[AKey, Nullity.Value]()

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
    val graph = cfg.buildControlFlowGraph(className, methodNode)
    var added = false
    val argumentTypes = Type.getArgumentTypes(methodNode.desc)
    val resultType = Type.getReturnType(methodNode.desc)
    val resultSort = resultType.getSort

    val isReferenceResult = resultSort == Type.OBJECT || resultSort == Type.ARRAY
    val isBooleanResult = Type.BOOLEAN_TYPE == resultType

    if (isReferenceResult || isBooleanResult) {
      if (graph.transitions.nonEmpty)  {
        val dfs = cfg.buildDFSTree(graph.transitions)
        val reducible = dfs.back.isEmpty || cfg.reducible(graph, dfs)
        if (reducible) {
          for (i <- argumentTypes.indices) {
            val argType = argumentTypes(i)
            val sort = argType.getSort
            if (sort == Type.OBJECT || sort == Type.ARRAY) {
              outSolver.addEquation(new InOutAnalysis(RichControlFlow(graph, dfs), InOut(i, Values.Null)).analyze())
              outSolver.addEquation(new InOutAnalysis(RichControlFlow(graph, dfs), InOut(i, Values.NotNull)).analyze())
              inSolver.addEquation(new NotNullInAnalysis(RichControlFlow(graph, dfs), i).analyze())
            }
            if (argType == Type.BOOLEAN_TYPE) {
              outSolver.addEquation(new InOutAnalysis(RichControlFlow(graph, dfs), InOut(i, Values.False)).analyze())
              outSolver.addEquation(new InOutAnalysis(RichControlFlow(graph, dfs), InOut(i, Values.True)).analyze())
            }
          }
          if (isReferenceResult) {
            outSolver.addEquation(new InOutAnalysis(RichControlFlow(graph, dfs), Out).analyze())
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
            outSolver.addEquation(Equation(AKey(method, InOut(i, Values.Null)), Final(Values.Top)))
            outSolver.addEquation(Equation(AKey(method, InOut(i, Values.NotNull)), Final(Values.Top)))
            inSolver.addEquation(Equation(AKey(method, In(i)), Final(Nullity.Nullable)))
          }
          if (argType == Type.BOOLEAN_TYPE) {
            outSolver.addEquation(Equation(AKey(method, InOut(i, Values.False)), Final(Values.Top)))
            outSolver.addEquation(Equation(AKey(method, InOut(i, Values.True)), Final(Values.Top)))
          }
        }
        if (isReferenceResult) {
          outSolver.addEquation(Equation(AKey(method, Out), Final(Values.Top)))
        }
      }
    }
  }

  def printToFile(f: java.io.File)(op: java.io.PrintWriter => Unit) {
    val p = new java.io.PrintWriter(f)
    try { op(p) } finally { p.close() }
  }

  def process(source: Source, outFile: String) {
    val indexStart = System.currentTimeMillis()

    println("indexing ...")
    source.process(this)
    val indexEnd = System.currentTimeMillis()

    println("solving ...")
    val outSolutions: Map[AKey, Values.Value] =
      outSolver.solve().filterNot(p => p._2 == Values.Top || p._2 == Values.Bot)

    val inSolutions: Map[AKey, Nullity.Value] =
      inSolver.solve().filter(_._2 == Nullity.NotNull)

    val solvingEnd = System.currentTimeMillis()

    println("saving to file ...")

    {
      val outs = ArrayBuffer[(String, String)]()
      for ((aKey, v) <- outSolutions) {
        aKey.direction match {
          case InOut(_, Values.Null)=>
            outs.append((aKey.toString.replace('/', '.'), v.toString))
          case _ =>
        }
      }

      val outsSorted = outs.sortBy(_._1)
      printToFile(new File(s"$outFile-null.txt")) {
        out =>
          for ((x, y) <- outsSorted) {
            out.println(x)
            out.println(y)
            out.println()
          }
      }
    }

    {
      val outs = ArrayBuffer[(String, String)]()
      for ((aKey, v) <- outSolutions) {
        aKey.direction match {
          case InOut(_, Values.NotNull) =>
            outs.append((aKey.toString.replace('/', '.'), v.toString))
          case _ =>
        }
      }

      val outsSorted = outs.sortBy(_._1)
      printToFile(new File(s"$outFile-notnull.txt")) {
        out =>
          for ((x, y) <- outsSorted) {
            out.println(x)
            out.println(y)
            out.println()
          }
      }
    }

    {
      val outs = ArrayBuffer[(String, String)]()
      for ((aKey, v) <- outSolutions) {
        aKey.direction match {
          case InOut(_, Values.False) =>
            outs.append((aKey.toString.replace('/', '.'), v.toString))
          case _ =>
        }
      }

      val outsSorted = outs.sortBy(_._1)
      printToFile(new File(s"$outFile-false.txt")) {
        out =>
          for ((x, y) <- outsSorted) {
            out.println(x)
            out.println(y)
            out.println()
          }
      }
    }

    {
      val outs = ArrayBuffer[(String, String)]()
      for ((aKey, v) <- outSolutions) {
        aKey.direction match {
          case InOut(_, Values.True) =>
            outs.append((aKey.toString.replace('/', '.'), v.toString))
          case _ =>
        }
      }

      val outsSorted = outs.sortBy(_._1)
      printToFile(new File(s"$outFile-true.txt")) {
        out =>
          for ((x, y) <- outsSorted) {
            out.println(x)
            out.println(y)
            out.println()
          }
      }
    }

    {
      val outs = ArrayBuffer[(String, String)]()
      for ((aKey, v) <- outSolutions) {
        (aKey.direction, v) match {
          case (Out, Values.NotNull) =>
            outs.append((aKey.toString.replace('/', '.'), v.toString))
          case (Out, Values.Null) =>
            outs.append((aKey.toString.replace('/', '.'), v.toString))
          case _ =>
        }
      }

      val outsSorted = outs.sortBy(_._1)
      printToFile(new File(s"$outFile-return.txt")) {
        out =>
          for ((x, y) <- outsSorted) {
            out.println(x)
            out.println(y)
            out.println()
          }
      }
    }

    {
      val outs = ArrayBuffer[String]()
      for ((parameter, v) <- inSolutions) {
        outs.append(parameter.toString.replace('/', '.'))
      }

      val outsSorted = outs.sorted
      printToFile(new File(s"$outFile-params.txt")) { out =>
        for (parameter <- outsSorted) {
          out.println(parameter)
        }
      }

    }

    val writingEnd = System.currentTimeMillis()

    println("====")
    println(s"indexing took ${(indexEnd - indexStart) / 1000.0} sec")
    println(s"solving took ${(solvingEnd - indexEnd) / 1000.0} sec")
    println(s"saving took ${(writingEnd - solvingEnd) / 1000.0} sec")

    println(s"${outSolutions.size} contracts")
  }

  def main(args: Array[String]) {
    if (args.length != 2) {
      println(s"Usage: faba.Main inputJar outputFile")
    } else {
      process(JarFileSource(new File(args(0))), args(1))
    }
  }

}
