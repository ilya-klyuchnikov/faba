package faba

import java.io.{File, PrintWriter}
import java.nio.file._
import java.nio.file.attribute.BasicFileAttributes

import faba.calls._
import faba.data._
import faba.engine._
import faba.source._
import org.objectweb.asm.Type

import scala.collection.mutable.ListBuffer
import scala.xml.PrettyPrinter

// TODO - single call resolver
class MainProcessor extends FabaProcessor {

  val notNullParamsCallsResolver = new CallResolver()
  val notNullParamsSolver =
    new StagedHierarchySolver[Key, Values.Value](Lattice(Values.NotNull, Values.Top), Values.Top)

  val nullableParamsCallResolver = new CallResolver()
  val nullableParamsSolver =
    new StagedHierarchySolver[Key, Values.Value](Lattice(Values.Null, Values.Top), Values.Top)

  val contractsCallsResolver = new CallResolver()
  val contractsSolver =
    new StagedHierarchySolver[Key, Values.Value](Lattice(Values.Bot, Values.Top), Values.Top)

  val nullableResultCallsResolver = new CallResolver()
  val nullableResultSolver =
    new StagedHierarchySolver[Key, Values.Value](Lattice(Values.Bot, Values.Null), Values.Bot)

  val purityCallsResolver = new CallResolver()
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

  def process(source: Source, outDir: String) {
    val pp = new PrettyPrinter(1000, 2)
    val sep = File.separatorChar

    val indexStart = System.currentTimeMillis()
    println("indexing ...")
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

    val resolveEnd = System.currentTimeMillis()

    println("solving ...")
    // solving everything
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
      printToFile(new File(s"$outDir$sep${pkg.replace('/', sep)}${sep}annotations.xml")) {
        _.println(pp.format(<root>{xmlAnnotations}</root>))
      }
    }
    val writingEnd = System.currentTimeMillis()
    println("====")
    println(s"indexing took ${(indexEnd - indexStart) / 1000.0} sec")
    println(s"resolve took ${(resolveEnd - indexEnd) / 1000.0} sec")
    println(s"solving took ${(solvingEnd - resolveEnd) / 1000.0} sec")
    println(s"saving took ${(writingEnd - solvingEnd) / 1000.0} sec")
    println(s"${debugSolutions.size} all contracts")
    println(s"${prodSolutions.size} prod contracts")
    println(s"${nullableParams.size} @Nullable parameters")
    println(s"${nullableResults.size} @Nullable results")
    println(s"${puritySolutions.size} @Pure methods")

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
