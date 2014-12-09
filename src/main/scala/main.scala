package faba

import java.io.{File, PrintWriter}
import java.nio.file._
import java.nio.file.attribute.BasicFileAttributes

import faba.analysis._
import faba.analysis.leakingParameters._
import faba.analysis.resultOrigins._
import faba.calls._
import faba.data._
import faba.engine._
import faba.source._
import org.objectweb.asm.Type

import org.objectweb.asm.tree.MethodNode
import org.objectweb.asm.tree.analysis.Frame

import scala.collection.mutable.ListBuffer
import scala.xml.PrettyPrinter

// TODO - current phase is migration to hierarchy support,
// after this migration is done there should be exactly one call resolver for all solvers
// the caveat: think how to handle calls
class MainProcessor extends FabaProcessor {

  val notNullParamsCallsResolver = new CallResolver()
  val notNullParamsSolver = new StagedHierarchySolver[Key, Values.Value](idle, Lattice(Values.NotNull, Values.Top))
  val nullableParamsSolver = new SimpleSolver[Key, Values.Value](idle, Lattice(Values.Null, Values.Top))
  val contractsSolver = new SimpleSolver[Key, Values.Value](idle, Lattice(Values.Bot, Values.Top))
  val nullableResultSolver = new NullableResultSimpleSolver[Key, Values.Value](idle, Lattice(Values.Bot, Values.Null))
  val puritySolver = new SimpleSolver[Key, Values.Value](idle, Lattice(Values.Pure, Values.Top))

  var notNullParamsTime: Long = 0
  var nullableParamsTime: Long = 0
  var nullableResultTime: Long = 0
  var outTime: Long = 0
  var nullTime: Long = 0
  var notNullTime: Long = 0
  var purityTime: Long = 0

  // Equations means that we get equations, not solutions as a result of analysis
  var outTimeEquations: Long = 0
  var nullTimeEquations: Long = 0
  var notNullTimeEquations: Long = 0

  // timeTop means that we get Final(Top) solution
  var outTimeTop: Long = 0
  var nullTimeTop: Long = 0
  var notNullTimeTop: Long = 0

  // timeNotNull means that we get Final(NotNull) solution
  var outTimeNotNull : Long = 0
  var nullTimeNotNull: Long = 0
  var notNullTimeNotNull: Long = 0

  var cfgTime: Long = 0
  var resultOriginsTime: Long = 0
  var resultOriginsTime2: Long = 0
  var reducibleTime: Long = 0
  var dfsTime: Long = 0
  var leakingParametersTime: Long = 0
  val processNullableParameters = true

  // origins.size < 32
  var smallOrigins: Long = 0
  // origins.size >= 32
  var largeOrigins: Long = 0

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
    val originSize = result.instructions.count(x => x) + result.parameters.count(x => x)
    if (originSize < 32)
      smallOrigins += 1
    else {
      largeOrigins += 1
    }
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

  override def purityEquation(method: Method, methodNode: MethodNode) = {
    val start = System.nanoTime()
    val result = super.purityEquation(method, methodNode)
    purityTime += System.nanoTime() - start
    result
  }

  override def notNullParamEquation(context: Context, i: Int) = {
    val start = System.nanoTime()
    val result = super.notNullParamEquation(context, i)
    notNullParamsTime += System.nanoTime() - start
    result
  }

  override def nullableParamEquation(context: Context, i: Int) = {
    val start = System.nanoTime()
    val result = super.nullableParamEquation(context, i)
    nullableParamsTime += System.nanoTime() - start
    result
  }

  override def notNullContractEquation(context: Context, resultOrigins: Origins, i: Int) = {
    val start = System.nanoTime()
    val result = super.notNullContractEquation(context, resultOrigins, i)
    val delta = System.nanoTime() - start
    notNullTime += delta
    result.rhs match {
      case Final(Values.Top) =>
        notNullTimeTop += delta
      case Final(Values.NotNull) =>
        notNullTimeNotNull += delta
      case Pending(_) =>
        notNullTimeEquations += delta
      case _ =>

    }
    result
  }

  override def nullContractEquation(context: Context, resultOrigins: Origins, i: Int) = {
    val start = System.nanoTime()
    val result = super.nullContractEquation(context, resultOrigins, i)
    val delta = System.nanoTime() - start
    nullTime += delta
    result.rhs match {
      case Final(Values.Top) =>
        nullTimeTop += delta
      case Final(Values.NotNull) =>
        nullTimeNotNull += delta
      case Pending(_) =>
        nullTimeEquations += delta
      case _ =>

    }
    result
  }

  override def outContractEquation(context: Context, resultOrigins: Origins) = {
    val start = System.nanoTime()
    val result = super.outContractEquation(context, resultOrigins)
    val delta = System.nanoTime() - start
    outTime += delta
    result.rhs match {
      case Final(Values.Top) =>
        outTimeTop += delta
      case Final(Values.NotNull) =>
        outTimeNotNull += delta
      case Pending(_) =>
        outTimeEquations += delta
      case _ =>

    }
    result
  }

  override def nullableResultEquation(className: String, methodNode: MethodNode, method: Method, origins: Origins, jsr: Boolean) = {
    val start = System.nanoTime()
    val result = super.nullableResultEquation(className, methodNode, method, origins, jsr)
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
    () //puritySolver.addEquation(eq)

  override def handleNotNullParamEquation(eq: Equation[Key, Value]) {
    //notNullParamsSolver.addEquation(eq)
    notNullParamsSolver.addMethodEquation(eq)
    notNullParamsSolver.getCalls(eq).foreach(notNullParamsCallsResolver.addCall)
  }

  override def handleNullableParamEquation(eq: Equation[Key, Value]): Unit =
    () // if (processNullableParameters) nullableParamsSolver.addEquation(eq)
  override def handleNotNullContractEquation(eq: Equation[Key, Value]): Unit =
    () //contractsSolver.addEquation(eq)
  override def handleNullContractEquation(eq: Equation[Key, Value]): Unit =
    () //contractsSolver.addEquation(eq)
  override def handleOutContractEquation(eq: Equation[Key, Value]): Unit =
    () //contractsSolver.addEquation(eq)
  override def handleNullableResultEquation(eq: Equation[Key, Value]): Unit =
    () //nullableResultSolver.addEquation(eq)

  override def mapClassInfo(classInfo: ClassInfo): Unit = {
    notNullParamsCallsResolver.addClassDeclaration(classInfo)
  }

  override def mapMethodInfo(methodInfo: MethodInfo) {
    notNullParamsCallsResolver.addMethodDeclaration(methodInfo)
  }

  def printToFile(f: File)(op: PrintWriter => Unit) {
    if (f.getParentFile != null)
      f.getParentFile.mkdirs()
    val p = new PrintWriter(f)
    try { op(p) } finally { p.close() }
  }

  def mkOverridableNotNullParamEquation(from: Method, to: Set[Method]): Map[Key, Set[Key]] = {
    var result = Map[Key, Set[Key]]()
    val parameterTypes = Type.getArgumentTypes(from.methodDesc)
    for (i <- parameterTypes.indices) {
      val argSort = parameterTypes(i).getSort
      val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
      if (isReferenceArg) {
        val fromKey = Key(from, In(i), ResolveDirection.Downward)
        result += (fromKey -> to.map(m => Key(m, In(i), ResolveDirection.Upward)))
      }
    }
    result
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
      notNullParamsCallsResolver.buildClassHierarchy()
      val resolveMap = notNullParamsCallsResolver.resolveCalls()
      // handling of calls
      notNullParamsSolver.bindCalls(resolveMap, Set())
      // handling of virtual methods
      val overridableMap = notNullParamsCallsResolver.bindOverridableMethods()
      for {(from, to) <- overridableMap} {
        val map = mkOverridableNotNullParamEquation(from, to)
        notNullParamsSolver.bindCalls(map, map.keys.toSet)
      }

      // val notNullParams = notNullParamsSolver.solve().filterNot(p => p._2 == Values.Top)
      val notNullParams = notNullParamsSolver.solve().filter(p => p._2 != Values.Top)
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
    println("====")
    println(s"pure=true      ${purityTime / 1000000} msec")
    println(s"nullableRes    ${nullableResultTime / 1000000} msec")
    println(s"results        ${outTime    / 1000000} msec")
    println(s"results?       ${outTimeEquations    / 1000000} msec")
    println(s"results+       ${outTimeTop    / 1000000} msec")
    println(s"results!       ${outTimeNotNull    / 1000000} msec")
    println("---")
    println(s"null           ${nullTime / 1000000} msec")
    println(s"null?          ${nullTimeEquations / 1000000} msec")
    println(s"null+          ${nullTimeTop / 1000000} msec")
    println(s"null!          ${nullTimeNotNull / 1000000} msec")
    println("---")
    println(s"!null          ${notNullTime / 1000000} msec")
    println(s"!null?         ${notNullTimeEquations / 1000000} msec")
    println(s"!null+         ${notNullTimeTop / 1000000} msec")
    println(s"!null!         ${notNullTimeNotNull / 1000000} msec")
    println("---")
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
    println("====")
    println(s"smallOrigins        $smallOrigins")
    println(s"largeOrigins        $largeOrigins")
  }

  // for testing - processing parameters only
  def process(source: Source): Annotations = {
    source.process(this)
    notNullParamsCallsResolver.buildClassHierarchy()
    val resolveMap = notNullParamsCallsResolver.resolveCalls()
    // handling of calls
    notNullParamsSolver.bindCalls(resolveMap, Set())
    // handling of virtual methods
    val overridableMap = notNullParamsCallsResolver.bindOverridableMethods()

    for {(from, to) <- overridableMap} {
      val map = mkOverridableNotNullParamEquation(from, to)
      notNullParamsSolver.bindCalls(map, map.keys.toSet)
    }

    val notNullParamSolutions: Map[Key, Values.Value] =
      notNullParamsSolver.solve().filterNot(p => p._2 == Values.Top || p._2 == Values.Bot)
    val nullableSolutions =
      nullableParamsSolver.solve().filter(p => p._2 == Values.Null).keys.toSet
    val contractSolutions: Map[Key, Values.Value] =
      contractsSolver.solve().filterNot(p => p._2 == Values.Top || p._2 == Values.Bot)
    AnnotationsUtil.toAnnotations(contractSolutions ++ notNullParamSolutions, nullableSolutions)
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
