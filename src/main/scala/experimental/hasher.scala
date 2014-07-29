package faba.experimental

import java.io.File
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file._

import faba.source.{MixedSource, JarFileSource, Source, Processor}
import org.objectweb.asm.Opcodes._
import org.objectweb.asm.{ClassVisitor, ClassReader}

import scala.collection.mutable.ListBuffer

object Hasher extends Processor {
  type H = String

  var collisions = 0
  var classesN: Long = 0
  var classes = Map[H, String]()
  var classCollisions = List[(String, String)]()

  def hashString(s: String): H = {
    import java.security.MessageDigest
    val messageDigest = MessageDigest.getInstance("MD5")
    messageDigest.update(s.getBytes)
    new String(messageDigest.digest())
  }

  override def processClass(classReader: ClassReader) {
    classesN += 1

    val className = classReader.getClassName
    val classHash = hashString(className)

    if (classes.contains(classHash) && classes(classHash) != className) {
      classCollisions ::= className -> classes(classHash)
    }
    classes += classHash -> className

    classReader.accept(new ClassVisitor(ASM5) {
      var hashes = Map[Int, String]()
      override def visitMethod(access: Int, name: String, desc: String, signature: String, exceptions: Array[String]) = {
        val mDesc = s"$name$desc"
        val hash = mDesc.hashCode
        if (hashes.contains(hash)) {
          println(s"${classReader.getClassName} ${hashes(hash)} $mDesc")
          collisions += 1
        }
        hashes += hash -> mDesc
        null
      }
    }, ClassReader.SKIP_CODE)
  }

  def main(args: Array[String]) {
    collisions = 0
    classesN = 0
    classes = Map()
    classCollisions = List[(String, String)]()
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
      MixedSource(sources.toList).process(this)
    }
    else {
      JarFileSource(new File(args(0))).process(this)
    }
    println(s"classes:    $classesN")
    println(s"methodCollisions: $collisions")
    println(s"classCollisions: $classCollisions")
    println(s"# of classCollisions: ${classCollisions.size}")
  }
}
