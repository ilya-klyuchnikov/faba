package faba.source

import java.io.{File, FileInputStream}
import java.util.jar.JarFile

import org.objectweb.asm._

import scala.collection.JavaConverters._
import scala.language.existentials

sealed trait Source {
  def process(processor: Processor): Unit
}

case class ClassSource(classes: Class[_]*) extends Source {
  override def process(processor: Processor): Unit =
    classes.foreach { clazz =>
      processor.processClass(new ClassReader(clazz.getCanonicalName))
    }
}

case class FileSource(file: File) extends Source {
  override def process(processor: Processor): Unit = {
    val is = new FileInputStream(file)
    try {
      processor.processClass(new ClassReader(is))
    } finally {
      is.close()
    }
  }
  override def toString = file.toString
}

case class JarFileSource(file: File) extends Source {
  override def process(processor: Processor): Unit = {
    val jarFile = new JarFile(file)
    for (entry <- jarFile.entries().asScala) {
      if (entry.getName.endsWith(".class")) {
        val is = jarFile.getInputStream(entry)
        try {
          processor.processClass(new ClassReader(is))
        } finally {
          is.close()
        }
      }
    }
  }

  override def toString = file.toString
}

case class MixedSource(sources: List[Source]) extends Source {
  override def process(processor: Processor): Unit =
    sources.foreach { s =>
      println(s"${new java.util.Date} processing $s")
      s.process(processor)
    }
}

trait Processor {
  def processClass(classReader: ClassReader): Unit
}
