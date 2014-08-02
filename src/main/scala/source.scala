package faba.source

import org.objectweb.asm._

import scala.language.existentials
import scala.collection.JavaConverters._

import java.io.File
import java.util.jar.JarFile

sealed trait Source {
  def process(processor: Processor): Unit
}

case class ClassSource(classes: Class[_]*) extends Source {
  override def process(processor: Processor): Unit =
    classes.foreach { clazz =>
      processor.processClass(new ClassReader(clazz.getCanonicalName))
    }
}

case class JarFileSource(file: File) extends Source {
  override def process(processor: Processor): Unit = {
    val jarFile = new JarFile(file)
    for (entry <- jarFile.entries().asScala) {
      if (entry.getName.endsWith(".class")) {
        val is = jarFile.getInputStream(entry)
        try {
          processor.processClass(new ClassReader(is))
        } catch {
          case e: Throwable =>
            println(s"error in $file / ${entry.getName}")
            e.printStackTrace()
        } finally {
          is.close()
        }
      }
    }
  }

  override def toString: String = file.toString
}

case class MixedSource(sources: List[Source]) extends Source {
  override def process(processor: Processor): Unit =
    for (source <- sources) {
      println(s"processing $source")
      try {
        source.process(processor)
      } catch {
        case e: Throwable =>
          println(s"error in $source")
          e.printStackTrace()
      }
    }
}

trait Processor {
  def processClass(classReader: ClassReader): Unit
}
