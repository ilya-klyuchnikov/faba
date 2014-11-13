package faba.experimental

import java.io.File
import java.nio.file._
import java.nio.file.attribute.BasicFileAttributes
import java.util.Date

import faba.FabaProcessor
import faba.data._
import faba.engine._
import faba.source.{MixedSource, JarFileSource, Source}
import org.objectweb.asm.Opcodes

import scala.collection.JavaConversions._
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object Statistics extends FabaProcessor {
  var eqs = 0

  private val dependencies =
    mutable.HashMap[Key, Set[Key]]()

  private val hierarchy =
    mutable.HashMap[String, Set[String]]()

  private val cardinalities =
    new Array[Int](31)

  private val outCardinalitiesWithHierarchy =
    new Array[Int](31)

  private val cardinalitiesWithHierarchy =
    new Array[Int](31)

  override def handleNotNullParamEquation(eq: Equation[Key, Value]) =
    handleEquation(eq)

  override def handleNotNullContractEquation(eq: Equation[Key, Value]) =
    handleEquation(eq)

  override def handleNullContractEquation(eq: Equation[Key, Value]) =
    handleEquation(eq)

  override def handleOutContractEquation(eq: Equation[Key, Value]) =
    handleEquation(eq)

  def handleEquation(eq: Equation[Key, Value]) {
    val key = eq.id
    eq.rhs match {
      case Pending(sop) =>
        eqs += 1
        dependencies(key) = dependencies.getOrElse(key, Set()) ++ sop.flatMap(_.elems)
      case Final(_) =>
        eqs += 1
        //cardinalities(0) += 1
    }
  }

  override def handleHierarchy(access: Int, thisName: String, superName: String) {
    // class, not an interface
    if (superName != null && (access & Opcodes.ACC_INTERFACE) == 0) {
      hierarchy(superName) = hierarchy.getOrElse(thisName, Set()) + thisName
    }
  }

  def allDependencies(key: Key): Set[Key] = {
    var visited = Set[Key]()
    val queue = mutable.Queue[Key]()

    queue.enqueue(key)
    visited += key
    while (queue.nonEmpty) {
      val k = queue.dequeue()
      val deps = dependencies.getOrElse(k.mkStable, Set()) ++ dependencies.getOrElse(k.mkUnstable, Set())
      for (dk <- deps if !visited(dk)) {
        visited += dk
        queue.enqueue(dk)
      }
    }
    if (visited.size == 0) {
      sys.error(key.toString)
    }
    visited
  }

  def allInheritors(className: String): Set[String] = {
    var visited = Set[String]()
    val queue = mutable.Queue[String]()

    queue.enqueue(className)
    visited += className
    while (queue.nonEmpty) {
      val cn = queue.dequeue()
      val inheritors = hierarchy.getOrElse(cn, Set())
      for (in <- inheritors if !visited(in)) {
        visited += in
        queue.enqueue(in)
      }
    }
    visited
  }

  def calculateDependencyStatistics() {

    println(eqs)
    println(dependencies.keySet.size)

    for (k <- dependencies.keySet) {
      val cardinality = allDependencies(k).size
      if (cardinality >= 30)
        cardinalities(30) += 1
      else
        cardinalities(cardinality) += 1
    }
    println("==== DEPENDENCIES ====")
    println(cardinalities.mkString(", "))
    println(s"ALL ${cardinalities.reduce(_ + _)}")
    println(cardinalities.zipWithIndex.map{case (card, i) => s"$i -> $card"}.mkString("\n"))
  }

  def calculateNotNullsWithHierarchy() {
    for (k <- dependencies.keySet) {
      k.direction match {
        case Out =>
          val method = k.method
          val thisClassName = method.internalClassName
          val ks = (allInheritors(thisClassName) + thisClassName).flatMap {
            cn => k.copy(method = method.copy(internalClassName = cn), stable = true) :: k.copy(method = method.copy(internalClassName = cn), stable = false) :: Nil
          }
          val allDeps: Set[Key] = ks.flatMap(allDependencies)
          val cardinality = allDeps.size
          if (cardinality >= 30)
            outCardinalitiesWithHierarchy(30) += 1
          else
            outCardinalitiesWithHierarchy(cardinality) += 1
        case _ =>
      }
    }
    println("==== DEPENDENCIES for out with hierarchy ====")
    println(outCardinalitiesWithHierarchy.mkString(", "))
    println(s"ALL ${outCardinalitiesWithHierarchy.reduce(_ + _)}")
    println(outCardinalitiesWithHierarchy.zipWithIndex.map{case (card, i) => s"$i -> $card"}.mkString("\n"))
  }

  def calculateAllWithHierarchy() {
    for (k <- dependencies.keySet) {
      val method = k.method
      val thisClassName = method.internalClassName
      val ks = (allInheritors(thisClassName) + thisClassName).flatMap {
        cn => k.copy(method = method.copy(internalClassName = cn), stable = true) :: k.copy(method = method.copy(internalClassName = cn), stable = false) :: Nil
      }
      val simpleDeps = allDependencies(k)
      val allDeps: Set[Key] = ks.flatMap(allDependencies)

      val inters = allDeps.intersect(simpleDeps)
      require(inters == simpleDeps, k.toString)
      val cardinality = allDeps.size
      if (cardinality >= 30)
        cardinalitiesWithHierarchy(30) += 1
      else
        cardinalitiesWithHierarchy(cardinality) += 1
    }
    println("==== DEPENDENCIES for all with hierarchy ====")
    println(cardinalitiesWithHierarchy.mkString(", "))
    println(s"ALL ${cardinalitiesWithHierarchy.reduce(_ + _)}")
    println(cardinalitiesWithHierarchy.zipWithIndex.map{case (card, i) => s"$i -> $card"}.mkString("\n"))
  }

  def process(source: Source) {
    println(s"${new Date()} indexing...")
    source.process(this)
    println(s"${new Date()} calculating statistics...")
    calculateDependencyStatistics()
    calculateAllWithHierarchy()
    calculateNotNullsWithHierarchy()
  }

  def main(args: Array[String]) {
    if (args(0) == "--dirs") {
      val sources = ListBuffer[Source]()
      for (d <- args.tail)
        Files.walkFileTree(FileSystems.getDefault.getPath(d), new SimpleFileVisitor[Path] {
          override def visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult = {
            if (file.toString.endsWith(".jar")) {
              println(s"adding $file")
              sources += JarFileSource(file.toFile)
            }
            super.visitFile(file, attrs)
          }
        })
      process(MixedSource(sources.toList))
    }
    else {
      process(JarFileSource(new File(args(0))))
    }
  }
}
