package faba

import java.io.{File, PrintWriter}
import java.nio.file._
import java.nio.file.attribute.BasicFileAttributes
import java.util.Date

import faba.calls._
import faba.data._
import faba.engine._
import faba.source._
import org.objectweb.asm.Type

import scala.collection.mutable.ListBuffer
import scala.xml.PrettyPrinter

// TODO - single call resolver
class MainProcessor(val noResolveViaHierarchy: Boolean) extends FabaProcessor {

  val notNullParamsCallsResolver = new CallResolver(noResolveViaHierarchy)
  val notNullParamsSolver =
    new StagedHierarchySolver[Key, Values.Value](Lattice(Values.NotNull, Values.Top), Values.Top)

  val nullableParamsCallResolver = new CallResolver(noResolveViaHierarchy)
  val nullableParamsSolver =
    new StagedHierarchySolver[Key, Values.Value](Lattice(Values.Null, Values.Top), Values.Top)

  val contractsCallsResolver = new CallResolver(noResolveViaHierarchy)
  val contractsSolver =
    new StagedHierarchySolver[Key, Values.Value](Lattice(Values.Bot, Values.Top), Values.Top)

  val nullableResultCallsResolver = new CallResolver(noResolveViaHierarchy)
  val nullableResultSolver =
    new StagedHierarchySolver[Key, Values.Value](Lattice(Values.Bot, Values.Null), Values.Bot)

  val purityCallsResolver = new CallResolver(noResolveViaHierarchy)
  val puritySolver =
    new StagedHierarchySolver[Key, Values.Value](Lattice(Values.Pure, Values.Top), Values.Top)

  val resolvers = List(
    notNullParamsCallsResolver,
    nullableParamsCallResolver,
    contractsCallsResolver,
    nullableResultCallsResolver,
    purityCallsResolver
  )

  override def handlePurityEquation(eq: Equation[Key, Value]) {
    puritySolver.addMethodEquation(eq)
    puritySolver.getCalls(eq).foreach(purityCallsResolver.addCall)
  }

  override def handleNotNullParamEquation(eq: Equation[Key, Value]) {
    notNullParamsSolver.addMethodEquation(eq)
    notNullParamsSolver.getCalls(eq).foreach(notNullParamsCallsResolver.addCall)
  }

  override def handleNullableParamEquation(eq: Equation[Key, Value]) {
    nullableParamsSolver.addMethodEquation(eq)
    nullableParamsSolver.getCalls(eq).foreach(nullableParamsCallResolver.addCall)
  }

  override def handleNotNullContractEquation(eq: Equation[Key, Value]) {
    contractsSolver.addMethodEquation(eq)
    contractsSolver.getCalls(eq).foreach(contractsCallsResolver.addCall)
  }

  override def handleNullContractEquation(eq: Equation[Key, Value]) {
    contractsSolver.addMethodEquation(eq)
    contractsSolver.getCalls(eq).foreach(contractsCallsResolver.addCall)
  }

  override def handleOutContractEquation(eq: Equation[Key, Value]) {
    contractsSolver.addMethodEquation(eq)
    contractsSolver.getCalls(eq).foreach(contractsCallsResolver.addCall)
  }

  override def handleNullableResultEquation(eq: Equation[Key, Value]) {
    nullableResultSolver.addMethodEquation(eq)
    nullableResultSolver.getCalls(eq).foreach(nullableResultCallsResolver.addCall)
  }

  override def mapClassInfo(classInfo: ClassInfo) {
    resolvers.foreach(_.addClassDeclaration(classInfo))
  }

  override def mapMethodInfo(methodInfo: MethodInfo) {
    resolvers.foreach(_.addMethodDeclaration(methodInfo))
  }

  def printToFile(f: File)(op: PrintWriter => Unit) {
    if (f.getParentFile != null)
      f.getParentFile.mkdirs()
    val p = new PrintWriter(f)
    try { op(p) } finally { p.close() }
  }

  /**
   *
   * @param from an overridable method
   * @param to a set of concrete methods `from` is resolved to
   * @return additional equations for a solver
   */
  def mkOverridableInEquation(from: Method, to: Set[Method]): Map[Key, Set[Key]] = { // TODO - extract this logic
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

  // TODO - need filter for result type - we are interested only in reference and (maybe) in boolean results
  def mkOverridableOutEquation(from: Method, to: Set[Method]): Map[Key, Set[Key]] = { // TODO - extract this logic
    val resultType = Type.getReturnType(from.methodDesc)
    val resultSort = resultType.getSort
    val isReferenceResult = resultSort == Type.OBJECT || resultSort == Type.ARRAY
    if (isReferenceResult)
      Map[Key, Set[Key]](
        Key(from, Out, ResolveDirection.Downward) -> to.map(m => Key(m, Out, ResolveDirection.Upward))
      )
    else
      Map[Key, Set[Key]]()
  }

  /**
   *
   * @param from an overridable method
   * @param to a set of concrete methods `from` is resolved to
   * @return additional equations for a solver
   */
  def mkOverridableContractEquation(from: Method, to: Set[Method]): Map[Key, Set[Key]] = {
    val methodResultSort = Type.getReturnType(from.methodDesc).getSort
    val isContractibleMethodResult =
      methodResultSort == Type.OBJECT || methodResultSort == Type.ARRAY || methodResultSort == Type.BOOLEAN
    var mapping = Map[Key, Set[Key]]()
    if (isContractibleMethodResult) {
      val parameterTypes = Type.getArgumentTypes(from.methodDesc)
      for (i <- parameterTypes.indices) {
        val argSort = parameterTypes(i).getSort
        val isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY
        if (isReferenceArg) {
          // null -> ... equation
          val nullFromKey = Key(from, InOut(i, Values.Null), ResolveDirection.Downward)
          mapping += (nullFromKey -> to.map(m => Key(m, InOut(i, Values.Null), ResolveDirection.Upward)))
          // !null -> ...
          val notNullFromKey = Key(from, InOut(i, Values.NotNull), ResolveDirection.Downward)
          mapping += (notNullFromKey -> to.map(m => Key(m, InOut(i, Values.NotNull), ResolveDirection.Upward)))
        }
      }
    }
    mapping
  }

  def process(source: Source): InferenceResult = {
    val pp = new PrettyPrinter(1000, 2)
    val sep = File.separatorChar

    val indexStart = System.currentTimeMillis()
    println(s"${new Date()} indexing ...")
    source.process(this)
    val indexEnd = System.currentTimeMillis()

    // handling hierarchy for @NotNull parameters
    notNullParamsCallsResolver.buildClassHierarchy()
    // handling of calls
    notNullParamsSolver.bindCalls(notNullParamsCallsResolver.resolveCalls(), Set())
    // handling of overridable methods for @NotNull parameters
    for {(from, to) <- notNullParamsCallsResolver.bindOverridableMethods()} {
      val map = mkOverridableInEquation(from, to)
      notNullParamsSolver.bindCalls(map, map.keys.toSet)
    }

    // handling nullableParams
    nullableParamsCallResolver.buildClassHierarchy()
    nullableParamsSolver.bindCalls(nullableParamsCallResolver.resolveCalls(), Set())
    // handling of overridable methods for @Nullable parameters
    for {(from, to) <- nullableParamsCallResolver.bindOverridableMethods()} {
      val map = mkOverridableInEquation(from, to)
      nullableParamsSolver.bindCalls(map, map.keys.toSet)
    }

    // handling hierarchy for Result analysis
    contractsCallsResolver.buildClassHierarchy()
    contractsSolver.bindCalls(contractsCallsResolver.resolveCalls(), Set())
    // handling of overridable methods for Result analysis
    for {(from, to) <- contractsCallsResolver.bindOverridableMethods()} {
      val outMap = mkOverridableOutEquation(from, to)
      contractsSolver.bindCalls(outMap, outMap.keys.toSet)
      val contractMap = mkOverridableContractEquation(from, to)
      contractsSolver.bindCalls(contractMap, contractMap.keys.toSet)
    }

    // nullable Result
    nullableResultCallsResolver.buildClassHierarchy()
    nullableResultSolver.bindCalls(nullableResultCallsResolver.resolveCalls(), Set())
    for {(from, to) <- nullableResultCallsResolver.bindOverridableMethods()} {
      val map = mkOverridableOutEquation(from, to)
      nullableResultSolver.bindCalls(map, map.keys.toSet)
    }

    // purity resolver
    purityCallsResolver.buildClassHierarchy()
    puritySolver.bindCalls(purityCallsResolver.resolveCalls(), Set())
    for {(from, to) <- purityCallsResolver.bindOverridableMethods()} {
      val map = mkOverridableOutEquation(from, to)
      puritySolver.bindCalls(map, map.keys.toSet)
    }

    println(s"${new Date()} solving ...")
    // solving everything
    val notNullParameters: Set[Key] =
      notNullParamsSolver.solve().filter(p => p._2 == Values.NotNull).keySet
    val nullableParameters: Set[Key] =
      nullableParamsSolver.solve().filter(p => p._2 == Values.Null).keySet

    // not filtered yet
    val allContracts: Map[Key, Values.Value] =
      contractsSolver.solve()
    val notNullMethods: Set[Key] =
      allContracts.filter(p => p._1.direction == Out && p._2 == Values.NotNull).keySet
    val nullableMethods: Set[Key] =
      nullableResultSolver.solve().filter(p => p._2 == Values.Null).keySet
    val pureMethods: Set[Key] =
      puritySolver.solve().filter(p => p._2 == Values.Pure).keySet
    val contractClauses: Map[Key, Values.Value] =
      allContracts.filter(p => p._1.direction.isInstanceOf[InOut] && p._2 != Values.Bot && p._2 != Values.Top)

    println(s"${new Date()} solved ...")

    InferenceResult(
      notNullParameters,
      nullableParameters,
      notNullMethods,
      nullableMethods,
      pureMethods,
      contractClauses
    )
  }

  def dumpResult(result: InferenceResult, outDir: String): Unit = {
    val pp = new PrettyPrinter(1000, 2)
    val sep = File.separatorChar
    for ((pkg, pkgResult) <- result.byPackage()) {
      val xmlAnnotations = XmlUtils.toXmlAnnotations(pkgResult, extras)
      printToFile(new File(s"$outDir$sep${pkg.replace('/', sep)}${sep}annotations.xml")) {
        _.println(pp.format(<root>{xmlAnnotations}</root>))
      }
    }
  }

  // for testing
  def testProcess(source: Source): Annotations = {
    source.process(this)
    notNullParamsCallsResolver.buildClassHierarchy()
    val resolveMap = notNullParamsCallsResolver.resolveCalls()
    // handling of calls
    notNullParamsSolver.bindCalls(resolveMap, Set())
    // handling of virtual methods
    val overridableMap = notNullParamsCallsResolver.bindOverridableMethods()

    for {(from, to) <- overridableMap} {
      val map = mkOverridableInEquation(from, to)
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

  def process(in: Source, out: String): Unit = {
    val inferenceResult = process(in)
    dumpResult(inferenceResult, out)
  }
}

object CmdUtils {
  def getIn(args: Array[String]): Source =
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
      MixedSource(sources.toList)
    }
    else {
      MixedSource(args.toList.map {f => JarFileSource(new File(f))})
    }

  def getInOut(args: Array[String]): (Source, String) =
    (getIn(args.init), args.last)
}

object Main extends MainProcessor(false) {
  def main(args: Array[String]) {
    //Thread.sleep(15000)
    val (in, out) = CmdUtils.getInOut(args)
    process(in, out)
  }
}
