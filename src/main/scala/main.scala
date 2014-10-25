package faba

import _root_.java.io.{PrintWriter, File}
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file._

import faba.asm.{Origins, ParamsValue}
import org.objectweb.asm.tree.MethodNode

import faba.cfg._
import faba.data._
import faba.engine._
import faba.source._
import org.objectweb.asm.tree.analysis.Frame
import scala.xml.PrettyPrinter
import scala.collection.mutable.ListBuffer

class MainProcessor extends FabaProcessor {

  val notNullParamsSolver = new Solver[Key, Values.Value](doNothing)(ELattice(Values.NotNull, Values.Top))
  val nullableParamsSolver = new Solver[Key, Values.Value](doNothing)(ELattice(Values.Null, Values.Top))
  val contractsSolver = new Solver[Key, Values.Value](doNothing)(ELattice(Values.Bot, Values.Top))
  val nullableResultSolver = new NullableResultSolver[Key, Values.Value](doNothing)(ELattice(Values.Bot, Values.Null))
  val puritySolver = new Solver[Key, Values.Value](doNothing)(ELattice(Values.Pure, Values.Top))

  var notNullParamsTime: Long = 0
  var nullableParamsTime: Long = 0
  var nullableResultTime: Long = 0
  var outTime: Long = 0
  var nullTime: Long = 0
  var notNullTime: Long = 0
  var purityTime: Long = 0
  var cfgTime: Long = 0
  var resultOriginsTime: Long = 0
  var resultOriginsTime2: Long = 0
  var reducibleTime: Long = 0
  var dfsTime: Long = 0
  var leakingParametersTime: Long = 0
  val processNullableParameters = true

  override def buildCFG(className: String, methodNode: MethodNode, jsr: Boolean) = {
    val start = System.nanoTime()
    val result = super.buildCFG(className, methodNode, jsr)
    cfgTime += System.nanoTime() - start
    result
  }

  override def buildResultOrigins(className: String, methodNode: MethodNode, frames: Array[Frame[ParamsValue]], graph: ControlFlowGraph) = {
    val start = System.nanoTime()
    val result = super.buildResultOrigins(className, methodNode, frames, graph)
    resultOriginsTime += System.nanoTime() - start
    result
  }

  override def isReducible(graph: ControlFlowGraph, dfs: DFSTree): Boolean = {
    val start = System.nanoTime()
    val result = super.isReducible(graph, dfs)
    reducibleTime += System.nanoTime() - start
    result
  }

  override def buildDFSTree(transitions: Array[List[Int]]): DFSTree = {
    val start = System.nanoTime()
    val result = super.buildDFSTree(transitions)
    dfsTime += System.nanoTime() - start
    result
  }

  override def purityEquation(method: Method, methodNode: MethodNode, stable: Boolean) = {
    val start = System.nanoTime()
    val result = super.purityEquation(method, methodNode, stable)
    purityTime += System.nanoTime() - start
    result
  }

  override def notNullParamEquation(richControlFlow: RichControlFlow, i: Int, stable: Boolean) = {
    val start = System.nanoTime()
    val result = super.notNullParamEquation(richControlFlow, i, stable)
    notNullParamsTime += System.nanoTime() - start
    result
  }

  override def nullableParamEquation(richControlFlow: RichControlFlow, i: Int, stable: Boolean) = {
    val start = System.nanoTime()
    val result = super.nullableParamEquation(richControlFlow, i, stable)
    nullableParamsTime += System.nanoTime() - start
    result
  }

  override def notNullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Origins, i: Int, stable: Boolean, noCycle: Boolean) = {
    val start = System.nanoTime()
    val result = super.notNullContractEquation(richControlFlow, resultOrigins, i, stable, noCycle)
    notNullTime += System.nanoTime() - start
    result
  }

  override def nullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Origins, i: Int, stable: Boolean, noCycle: Boolean) = {
    val start = System.nanoTime()
    val result = super.nullContractEquation(richControlFlow, resultOrigins, i, stable, noCycle)
    nullTime += System.nanoTime() - start
    result
  }

  override def outContractEquation(richControlFlow: RichControlFlow, resultOrigins: Origins, stable: Boolean, noCycle: Boolean) = {
    val start = System.nanoTime()
    val result = super.outContractEquation(richControlFlow, resultOrigins, stable, noCycle)
    outTime += System.nanoTime() - start
    result
  }

  override def nullableResultEquation(className: String, methodNode: MethodNode, method: Method, origins: Origins, stable: Boolean, jsr: Boolean) = {
    val start = System.nanoTime()
    val result = super.nullableResultEquation(className, methodNode, method, origins, stable, jsr)
    nullableResultTime += System.nanoTime() - start
    result
  }

  override def leakingParameters(className: String, methodNode: MethodNode, jsr: Boolean) = {
    val start = System.nanoTime()
    val result = super.leakingParameters(className, methodNode, jsr)
    leakingParametersTime += System.nanoTime() - start
    result
  }

  override def handlePurityEquation(eq: Equation[Key, Value]): Unit =
    puritySolver.addEquation(eq)
  override def handleNotNullParamEquation(eq: Equation[Key, Value]): Unit =
    notNullParamsSolver.addEquation(eq)
  override def handleNullableParamEquation(eq: Equation[Key, Value]): Unit = {
    if (processNullableParameters)
      nullableParamsSolver.addEquation(eq)
  }
  override def handleNotNullContractEquation(eq: Equation[Key, Value]): Unit =
    contractsSolver.addEquation(eq)
  override def handleNullContractEquation(eq: Equation[Key, Value]): Unit =
    contractsSolver.addEquation(eq)
  override def handleOutContractEquation(eq: Equation[Key, Value]): Unit =
    contractsSolver.addEquation(eq)
  override def handleNullableResultEquation(eq: Equation[Key, Value]): Unit =
    nullableResultSolver.addEquation(eq)

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
    if (outDir != null) {
      val notNullParams = notNullParamsSolver.solve().filterNot(p => p._2 == Values.Top)
      val nullableParams = nullableParamsSolver.solve().filterNot(p => p._2 == Values.Top)
      val contracts = contractsSolver.solve()
      val nullableResults = nullableResultSolver.solve().filter(p => p._2 == Values.Null)

      val dupKeys = notNullParams.keys.toSet intersect nullableParams.keys.toSet
      for (k <- dupKeys) println(s"$k both @Nullable and @NotNull")

      val debugSolutions: Map[Key, Values.Value] =
        notNullParams ++ nullableParams ++ contracts
      val solvingEnd = System.currentTimeMillis()
      println("saving to file ...")

      val prodSolutions: Map[Key, Values.Value] =
        debugSolutions.filterNot(p => p._2 == Values.Top || p._2 == Values.Bot)

      val byPackageProd: Map[String, Map[Key, Values.Value]] =
        prodSolutions.groupBy(_._1.method.internalPackageName)

      val byPackageNullableResultSolutions: Map[String, Map[Key, Values.Value]] =
        nullableResults.groupBy(_._1.method.internalPackageName)

      val puritySolutions =
        puritySolver.solve().filterNot(p => p._2 == Values.Top || p._2 == Values.Bot)

      val byPackagePuritySolutions: Map[String, Map[Key, Values.Value]] =
        puritySolutions.groupBy(_._1.method.internalPackageName)

      // combining all packages
      val pkgs =
        byPackageProd.keys ++ byPackageNullableResultSolutions.keys ++ byPackagePuritySolutions.keys

      for (pkg <- pkgs) {
        val xmlAnnotations =
          XmlUtils.toXmlAnnotations(
            byPackageProd.getOrElse(pkg, Map()),
            byPackageNullableResultSolutions.getOrElse(pkg, Map()),
            byPackagePuritySolutions.getOrElse(pkg, Map()),
            extras,
            debug = false)
        printToFile(new File(s"$outDir${sep}${pkg.replace('/', sep)}${sep}annotations.xml")) { out =>
          out.println(pp.format(<root>{xmlAnnotations}</root>))
        }
      }
      val writingEnd = System.currentTimeMillis()

      println(s"solving took ${(solvingEnd - indexEnd) / 1000.0} sec")
      println(s"saving took ${(writingEnd - solvingEnd) / 1000.0} sec")
      println(s"${debugSolutions.size} all contracts")
      println(s"${prodSolutions.size} prod contracts")
      println(s"${nullableParams.size} @Nullable parameters")
      println(s"${nullableResults.size} @Nullable results")
      println(s"${puritySolutions.size} @Pure methods")
    }

    println("====")
    println(s"indexing took ${(indexEnd - indexStart) / 1000.0} sec")
    println("INDEXING TIME")
    println(s"notNullParams  ${notNullParamsTime / 1000000} msec")
    println(s"nullableParams ${nullableParamsTime / 1000000} msec")
    println(s"results        ${outTime    / 1000000} msec")
    println(s"nullableRes    ${nullableResultTime / 1000000} msec")
    println(s" null->...     ${nullTime / 1000000} msec")
    println(s"!null->...     ${notNullTime / 1000000} msec")
    println(s"pure=true      ${purityTime / 1000000} msec")
    println("====")
    println(s"cfg            ${cfgTime / 1000000} msec")
    println(s"origins        ${resultOriginsTime / 1000000} msec")
    println(s"dfs            ${dfsTime / 1000000} msec")
    println(s"reducible      ${reducibleTime / 1000000} msec")
    println(s"leakingParams  ${leakingParametersTime / 1000000} msec")
    println(s"simpleTime0    ${simpleTime / 1000000} msec")
    println(s"complexTime    ${complexTime / 1000000} msec")
    println("====")
    println(s"$simpleMethods  simple methods")
    println(s"$complexMethods complex methods")
    println("====")
    println(s"$cycleMethods    cycle methods")
    println(s"$nonCycleMethods non cycle methods")
    println("====")
    println(s"cycleTime        ${cycleTime / 1000000} msec")
    println(s"nonCycleTime     ${nonCycleTime / 1000000} msec")
  }

  def process(source: Source): Annotations = {
    source.process(this)
    val solutions: Map[Key, Values.Value] =
      (notNullParamsSolver.solve() ++ contractsSolver.solve()).filterNot(p => p._2 == Values.Top || p._2 == Values.Bot)
    data.Utils.toAnnotations(solutions)
  }
}

object Main extends MainProcessor {

  def main(args: Array[String]) {
    //Thread.sleep(15000)
    if (args(0) == "--dirs") {
      val sources = ListBuffer[Source]()
      for (d <- args.tail)
        Files.walkFileTree(FileSystems.getDefault.getPath(d), new SimpleFileVisitor[Path] {
          override def visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult = {
            if (file.toString.endsWith(".jar")) {
              println(s"adding $file")
              sources += JarFileSource(file.toFile)
            }
            if (file.toString.endsWith(".class")) {
              println(s"adding $file")
              sources += FileSource(file.toFile)
            }
            super.visitFile(file, attrs)
          }
        })
      process(MixedSource(sources.toList), null)
    }
    else {
      process(MixedSource(args.toList.init.map {f => JarFileSource(new File(f))}), args.last)
    }
  }
}
