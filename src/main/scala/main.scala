package faba

import faba.analysis.LimitReachedException
import faba.contracts.InOutAnalysis
import faba.engine.{Final, Equation, ELattice, Solver}
import faba.parameters.{NotNullInAnalysis, NullableInAnalysis}
import org.objectweb.asm.tree.MethodNode
import _root_.java.io.{PrintWriter, File}

import faba.cfg._
import faba.data._
import faba.source._
import scala.xml.PrettyPrinter

case class Debug(key: Key, ticks: Int, time: Long)

class MainProcessor extends FabaProcessor {

  val notNullParamsSolver = new Solver[Key, Values.Value]()(ELattice(Values.NotNull, Values.Top))
  val nullableParamsSolver = new Solver[Key, Values.Value]()(ELattice(Values.Null, Values.Top))
  val contractsSolver = new Solver[Key, Values.Value]()(ELattice(Values.Bot, Values.Top))

  var notNullParamsTime: Long = 0
  var nullableParamsTime: Long = 0
  var outTime: Long = 0
  var falseTime: Long = 0
  var trueTime: Long = 0
  var nullTime: Long = 0
  var notNullTime: Long = 0
  var cfgTime: Long = 0
  var resultOriginsTime: Long = 0
  var reducibleTime: Long = 0
  var dfsTime: Long = 0
  var leakingParametersTime: Long = 0
  val processNullableParameters = true

  var notNullParameterTicks =
    List[Debug]()
  var nullableParameterTicks =
    List[Debug]()
  var notNullResultTicks =
    List[Debug]()
  var contractTicks =
    List[Debug]()

  var limitReached = 0

  override def buildCFG(className: String, methodNode: MethodNode) = {
    val start = System.nanoTime()
    val result = super.buildCFG(className, methodNode)
    cfgTime += System.nanoTime() - start
    result
  }

  override def buildResultOrigins(className: String, methodNode: MethodNode) = {
    val start = System.nanoTime()
    val result = super.buildResultOrigins(className, methodNode)
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

  override def notNullParamEquation(richControlFlow: RichControlFlow, i: Int, stable: Boolean) = {
    val start = System.nanoTime()
    val analyser = new NotNullInAnalysis(richControlFlow, In(i), stable)
    val result = try {
      analyser.analyze()
    } catch {
      case LimitReachedException =>
        limitReached += 1
        Equation(analyser.aKey, Final(Values.Top))
    }
    val time = System.nanoTime() - start
    notNullParameterTicks ::= Debug(result.id, analyser.lastId(), time)
    notNullParamsTime += time
    result
  }

  override def nullableParamEquation(richControlFlow: RichControlFlow, i: Int, stable: Boolean) = {
    val start = System.nanoTime()
    val analyser = new NullableInAnalysis(richControlFlow, In(i), stable)
    val result = try {
      analyser.analyze()
    } catch {
      case LimitReachedException =>
        limitReached += 1
        Equation(analyser.aKey, Final(Values.Top))
    }
    val time = System.nanoTime() - start
    nullableParameterTicks ::= Debug(result.id, analyser.lastId(), time)
    nullableParamsTime += time
    result
  }

  override def notNullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int, stable: Boolean) = {
    val start = System.nanoTime()
    val analyser = new InOutAnalysis(richControlFlow, InOut(i, Values.NotNull), resultOrigins, stable)
    val result = try {
      analyser.analyze()
    } catch {
      case LimitReachedException =>
        limitReached += 1
        Equation(analyser.aKey, Final(Values.Top))
    }
    val time = System.nanoTime() - start
    contractTicks ::= Debug(result.id, analyser.lastId(), time)
    notNullTime += time
    result
  }

  override def nullContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int, stable: Boolean) = {
    val start = System.nanoTime()
    val analyser = new InOutAnalysis(richControlFlow, InOut(i, Values.Null), resultOrigins, stable)
    val result = try {
      analyser.analyze()
    } catch {
      case LimitReachedException =>
        limitReached += 1
        Equation(analyser.aKey, Final(Values.Top))
    }
    val time = System.nanoTime() - start
    contractTicks ::= Debug(result.id, analyser.lastId(), time)
    nullTime += time
    result
  }

  override def trueContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int, stable: Boolean) = {
    val start = System.nanoTime()
    val analyser = new InOutAnalysis(richControlFlow, InOut(i, Values.True), resultOrigins, stable)
    val result = try {
      analyser.analyze()
    } catch {
      case LimitReachedException =>
        limitReached += 1
        Equation(analyser.aKey, Final(Values.Top))
    }
    val time = System.nanoTime() - start
    contractTicks ::= Debug(result.id, analyser.lastId(), time)
    trueTime += time
    result
  }

  override def falseContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], i: Int, stable: Boolean) = {
    val start = System.nanoTime()
    val analyser = new InOutAnalysis(richControlFlow, InOut(i, Values.False), resultOrigins, stable)
    val result = try {
      analyser.analyze()
    } catch {
      case LimitReachedException =>
        limitReached += 1
        Equation(analyser.aKey, Final(Values.Top))
    }
    val time = System.nanoTime() - start
    contractTicks ::= Debug(result.id, analyser.lastId(), time)
    falseTime += time
    result
  }

  override def outContractEquation(richControlFlow: RichControlFlow, resultOrigins: Set[Int], stable: Boolean) = {
    val start = System.nanoTime()
    val analyser = new InOutAnalysis(richControlFlow, Out, resultOrigins, stable)
    val result = try {
      analyser.analyze()
    } catch {
      case LimitReachedException =>
        limitReached += 1
        Equation(analyser.aKey, Final(Values.Top))
    }
    val time = System.nanoTime() - start
    notNullResultTicks ::= Debug(result.id, analyser.lastId(), time)
    outTime += time
    result
  }

  override def leakingParameters(className: String, methodNode: MethodNode): (Set[Int], Set[Int]) = {
    val start = System.nanoTime()
    val result = super.leakingParameters(className, methodNode)
    leakingParametersTime += System.nanoTime() - start
    result
  }

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
  override def handleTrueContractEquation(eq: Equation[Key, Value]): Unit =
    contractsSolver.addEquation(eq)
  override def handleFalseContractEquation(eq: Equation[Key, Value]): Unit =
    contractsSolver.addEquation(eq)
  override def handleOutContractEquation(eq: Equation[Key, Value]): Unit =
    contractsSolver.addEquation(eq)

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
    val notNullParams = notNullParamsSolver.solve().filterNot(p => p._2 == Values.Top)
    val nullableParams = nullableParamsSolver.solve().filterNot(p => p._2 == Values.Top)
    val contracts = contractsSolver.solve()

    val dupKeys = notNullParams.keys.toSet intersect nullableParams.keys.toSet
    for (k <- dupKeys) println(s"$k both @Nullable and @NotNull")

    val debugSolutions: Map[Key, Values.Value] =
      notNullParams ++ nullableParams ++ contracts
    val solvingEnd = System.currentTimeMillis()
    println("saving to file ...")

    /*
    val byPackage: Map[String, Map[Key, Values.Value]] =
      debugSolutions.groupBy(_._1.method.internalPackageName)

    for ((pkg, solution) <- byPackage) {
      val xmlAnnotations = XmlUtils.toXmlAnnotations(solution, extras, debug = true)
      printToFile(new File(s"$outDir-debug${sep}${pkg.replace('/', sep)}${sep}annotations.xml")) { out =>
        out.println(pp.format(<root>{xmlAnnotations}</root>))
      }
    }*/

    val prodSolutions: Map[Key, Values.Value] =
      debugSolutions.filterNot(p => p._2 == Values.Top || p._2 == Values.Bot)

    val byPackageProd: Map[String, Map[Key, Values.Value]] =
      prodSolutions.groupBy(_._1.method.internalPackageName)

    for ((pkg, solution) <- byPackageProd) {
      val xmlAnnotations = XmlUtils.toXmlAnnotations(solution, extras, debug = false)
      printToFile(new File(s"$outDir${sep}${pkg.replace('/', sep)}${sep}annotations.xml")) { out =>
        out.println(pp.format(<root>{xmlAnnotations}</root>))
      }
    }

    val writingEnd = System.currentTimeMillis()

    println("====")
    println(s"indexing took ${(indexEnd - indexStart) / 1000.0} sec")
    println(s"solving took ${(solvingEnd - indexEnd) / 1000.0} sec")
    println(s"saving took ${(writingEnd - solvingEnd) / 1000.0} sec")
    println(s"${debugSolutions.size} all contracts")
    println(s"${prodSolutions.size} prod contracts")
    println("INDEXING TIME")
    println(s"notNullParams  ${notNullParamsTime / 1000000} msec")
    println(s"nullableParams ${nullableParamsTime / 1000000} msec")
    println(s"results        ${outTime    / 1000000} msec")
    println(s"false          ${falseTime / 1000000} msec")
    println(s"true           ${trueTime / 1000000} msec")
    println(s"null           ${nullTime / 1000000} msec")
    println(s"!null          ${notNullTime / 1000000} msec")
    println(s"cfg            ${cfgTime / 1000000} msec")
    println(s"origins        ${resultOriginsTime / 1000000} msec")
    println(s"dfs            ${dfsTime / 1000000} msec")
    println(s"reducible      ${reducibleTime / 1000000} msec")
    println(s"leakingParams  ${leakingParametersTime / 1000000} msec")
    println(s"limitReached   $limitReached")

    printTicks("@Nullable parameters", nullableParameterTicks)
    printTicks("@NotNull parameters", notNullParameterTicks)
    printTicks("@NotNull results", notNullResultTicks)
    printTicks("@Contract", contractTicks)
  }

  def printTicks(name: String, ticks: List[Debug]) {
    println(s"======== $name ========")
    val totalTicks = ticks.map(_.ticks).sum
    val totalTime = ticks.map(_.time).sum
    val avgTicks = if (ticks.size > 0) totalTicks / ticks.size else 0
    val avgTime = if (ticks.size > 0) totalTime / ticks.size else 0
    println(s"total ticks: $totalTicks")
    println(s"avg ticks:   $avgTicks")
    println(s"total time:  ${totalTime / 1000000} msec")
    println(s"avg time:    ${avgTime/1000000.0} msec")
    for (info <- ticks.sortBy(_.ticks).reverse.take(20)) {
      println(info.key)
      println(s"    ${info.ticks} ticks")
      println(s"    ${info.time/1000000} msec")
    }
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
