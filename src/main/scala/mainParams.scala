package faba

import org.objectweb.asm.{MethodVisitor, Opcodes, ClassVisitor, ClassReader, Type}
import org.objectweb.asm.tree.MethodNode
import _root_.java.io.{PrintWriter, File}

import faba.cfg._
import faba.data._
import faba.engine._
import faba.source._
import scala.xml.PrettyPrinter

// inferrer that works with parameter only
object MainParams extends Processor {

  import faba.parameters._

  val solver = new Solver[Key, Values.Value]()

  var methods: Long = 0
  var params: Long = 0
  var paramsTime: Long = 0
  var cfgTime: Long = 0
  var reducibleTime: Long = 0
  var dfsTime: Long = 0

  def time(f: => Unit): Long = {
    val start = System.currentTimeMillis()
    f
    System.currentTimeMillis() - start
  }

  def buildCFG(className: String, methodNode: MethodNode) = {
    val start = System.currentTimeMillis()
    val result = cfg.buildControlFlowGraph(className, methodNode)
    cfgTime += System.currentTimeMillis() - start
    result
  }

  def isReducible(graph: ControlFlowGraph, dfs: DFSTree): Boolean = {
    val start = System.currentTimeMillis()
    val result = cfg.reducible(graph, dfs)
    reducibleTime += System.currentTimeMillis() - start
    result
  }

  def buildDFSTree(transitions: Array[List[Int]]): DFSTree = {
    val start = System.currentTimeMillis()
    val result = cfg.buildDFSTree(transitions)
    dfsTime += System.currentTimeMillis() - start
    result
  }

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
    methods += 1

    val graph = buildCFG(className, methodNode)

    var added = false
    val argumentTypes = Type.getArgumentTypes(methodNode.desc)

    if (graph.transitions.nonEmpty)  {
      val dfs = buildDFSTree(graph.transitions)
      val reducible = dfs.back.isEmpty || isReducible(graph, dfs)
      if (reducible) {
        for (i <- argumentTypes.indices) {
          val argType = argumentTypes(i)
          val argSort = argType.getSort
          val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
          if (isReferenceArg) {
            paramsTime += time(solver.addEquation(new NotNullInAnalysis(RichControlFlow(graph, dfs), In(i)).analyze()))
            params += 1
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
        val argType: Type = argumentTypes(i)
        val sort = argType.getSort
        if (sort == Type.OBJECT || sort == Type.ARRAY) {
          solver.addEquation(Equation(Key(method, In(i)), Final(Values.Top)))
          params += 1
        }
      }
    }
  }

  def printToFile(f: File)(op: PrintWriter => Unit) {
    if (f.getParentFile != null)
      f.getParentFile.mkdirs()
    val p = new PrintWriter(f)
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
    val solutions: Map[Key, Values.Value] =
      solver.solve().filterNot(p => p._2 == Values.Top || p._2 == Values.Bot)
    val solvingEnd = System.currentTimeMillis()
    println("saving to file ...")

    val byPackage: Map[String, Map[Key, Values.Value]] =
      solutions.groupBy(_._1.method.internalPackageName)

    for ((pkg, solution) <- byPackage) {
      val xmlAnnotations = XmlUtils.toXmlAnnotations(solution)
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
    println(s"params  $params")
    println(s"methods  $methods")
    println("INDEXING TIME")
    println(s"paramsTime  ${paramsTime / 1000.0} sec")
    println(s"cfg         ${cfgTime / 1000.0} sec")
    println(s"dfs         ${dfsTime / 1000.0} sec")
    println(s"reducible   ${reducibleTime / 1000.0} sec")
  }

  def main(args: Array[String]) {
    if (args.length != 2) {
      println(s"Usage: faba.MainParams inputJar outputDir")
    } else {
      process(JarFileSource(new File(args(0))), args(1))
    }
  }

}
