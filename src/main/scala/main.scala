package faba

import org.objectweb.asm.tree.MethodNode
import _root_.java.io.{PrintWriter, File}

import faba.cfg._
import faba.data._
import faba.source._
import scala.xml.PrettyPrinter

class MainProcessor extends FabaProcessor {

  var paramsTime: Long = 0
  var outTime: Long = 0
  var falseTime: Long = 0
  var trueTime: Long = 0
  var nullTime: Long = 0
  var notNullTime: Long = 0
  var cfgTime: Long = 0
  var resultOriginsTime: Long = 0
  var reducibleTime: Long = 0
  var dfsTime: Long = 0

  override def buildCFG(className: String, methodNode: MethodNode) = {
    val start = System.currentTimeMillis()
    val result = super.buildCFG(className, methodNode)
    cfgTime += System.currentTimeMillis() - start
    result
  }

  override def buildResultOrigins(className: String, methodNode: MethodNode) = {
    val start = System.currentTimeMillis()
    val result = super.buildResultOrigins(className, methodNode)
    resultOriginsTime += System.currentTimeMillis() - start
    result
  }

  override def isReducible(graph: ControlFlowGraph, dfs: DFSTree): Boolean = {
    val start = System.currentTimeMillis()
    val result = super.isReducible(graph, dfs)
    reducibleTime += System.currentTimeMillis() - start
    result
  }

  override def buildDFSTree(transitions: Array[List[Int]]): DFSTree = {
    val start = System.currentTimeMillis()
    val result = super.buildDFSTree(transitions)
    dfsTime += System.currentTimeMillis() - start
    result
  }

  override def notNullParamEquation(richControlFlow: RichControlFlow, i: Int) = {
    val start = System.currentTimeMillis()
    val result = super.notNullParamEquation(richControlFlow, i)
    paramsTime += System.currentTimeMillis() - start
    result
  }

  override def notNullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int) = {
    val start = System.currentTimeMillis()
    val result = super.notNullContractEquation(richControlFlow, resultOrigins, i)
    notNullTime += System.currentTimeMillis() - start
    result
  }

  override def nullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int) = {
    val start = System.currentTimeMillis()
    val result = super.nullContractEquation(richControlFlow, resultOrigins, i)
    nullTime += System.currentTimeMillis() - start
    result
  }

  override def trueContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int) = {
    val start = System.currentTimeMillis()
    val result = super.trueContractEquation(richControlFlow, resultOrigins, i)
    trueTime += System.currentTimeMillis() - start
    result
  }

  override def falseContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int) = {
    val start = System.currentTimeMillis()
    val result = super.falseContractEquation(richControlFlow, resultOrigins, i)
    falseTime += System.currentTimeMillis() - start
    result
  }

  override def outContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int]) = {
    val start = System.currentTimeMillis()
    val result = super.outContractEquation(richControlFlow, resultOrigins)
    outTime += System.currentTimeMillis() - start
    result
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
      val xmlAnnotations = Utils.toXmlAnnotations(solution)
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
    println("INDEXING TIME")
    println(s"params      ${paramsTime / 1000.0} sec")
    println(s"results     ${outTime / 1000.0} sec")
    println(s"false       ${falseTime / 1000.0} sec")
    println(s"true        ${trueTime / 1000.0} sec")
    println(s"null        ${nullTime / 1000.0} sec")
    println(s"!null       ${notNullTime / 1000.0} sec")
    println(s"cfg         ${cfgTime / 1000.0} sec")
    println(s"origins     ${resultOriginsTime / 1000.0} sec")
    println(s"dfs         ${dfsTime / 1000.0} sec")
    println(s"reducible   ${reducibleTime / 1000.0} sec")
  }

  def process(source: Source): Annotations = {
    source.process(this)
    val solutions = solver.solve().filterNot(p => p._2 == Values.Top || p._2 == Values.Bot)
    Utils.toAnnotations(solutions)
  }
}

object Main extends MainProcessor {
  def main(args: Array[String]) {
    if (args.length != 2) {
      println(s"Usage: faba.Main inputJar outputDir")
    } else {
      process(JarFileSource(new File(args(0))), args(1))
    }
  }
}

object MainParams extends MainProcessor {
  override val processContracts = false
  def main(args: Array[String]) {
    if (args.length != 2) {
      println(s"Usage: faba.MainParams inputJar outputDir")
    } else {
      process(JarFileSource(new File(args(0))), args(1))
    }
  }
}
