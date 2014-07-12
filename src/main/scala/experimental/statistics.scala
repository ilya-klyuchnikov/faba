package faba.experimental

import java.io.File
import java.nio.file._
import java.nio.file.attribute.BasicFileAttributes
import java.util.Date

import faba.FabaProcessor
import faba.data.Key
import faba.data.Value
import faba.engine._
import faba.source.{MixedSource, JarFileSource, Source}

import scala.collection.JavaConversions._
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object Statistics extends FabaProcessor {
  var eqs = 0

  private val dependencies =
    mutable.HashMap[Key, Set[Key]]()

  private val cardinalities =
    new Array[Int](31)

  override def handleNotNullParamEquation(eq: Equation[Key, Value]) =
    handleEquation(eq)

  override def handleNotNullContractEquation(eq: Equation[Key, Value]) =
    handleEquation(eq)

  override def handleNullContractEquation(eq: Equation[Key, Value]) =
    handleEquation(eq)

  override def handleTrueContractEquation(eq: Equation[Key, Value]) =
    handleEquation(eq)

  override def handleFalseContractEquation(eq: Equation[Key, Value]) =
    handleEquation(eq)

  override def handleOutContractEquation(eq: Equation[Key, Value]) =
    handleEquation(eq)

  def handleEquation(eq: Equation[Key, Value]) {
    val key = eq.id
    eq.rhs match {
      case Pending(sop) =>
        eqs += 1
        dependencies(key) = dependencies.getOrElse(key, Set()) ++ sop.flatMap(_.ids)
      case Final(_) =>
        eqs += 1
        cardinalities(0) += 1
    }
  }

  def allDependencies(key: Key): Set[Key] = {
    var visited = Set[Key]()
    val queue = mutable.Queue[Key]()

    queue.enqueue(key)
    visited += key
    while (queue.nonEmpty) {
      val k = queue.dequeue()
      // todo - more fine-grained handling of stable/unstable keys
      val deps = dependencies.getOrElse(k.mkStable, Set()) ++ dependencies.getOrElse(k.mkUnstable, Set())
      for (dk <- deps if !visited(dk)) {
        visited += dk
        queue.enqueue(dk)
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
  }

  def process(source: Source) {
    println(s"${new Date()} indexing...")
    source.process(this)
    println(s"${new Date()} calculating statistics...")
    calculateDependencyStatistics()
    println(cardinalities.zipWithIndex.map{case (card, i) => s"$i -> $card"}.mkString("\n"))
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
