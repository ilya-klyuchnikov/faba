package faba.test

import annotations.{ExpectLocalEffect, ExpectPure}
import data.PurityData
import faba.MainProcessor
import faba.asm.PurityAnalysis
import faba.data.{Key, Method, Out}
import faba.source.ClassSource
import org.objectweb.asm.Type
import org.scalatest.{FunSuite, Matchers}

// NB: works with stable keys only
class PuritySuite extends FunSuite with Matchers {

  test("PurityData.class") {
    checkInference(classOf[PurityData])
  }

  def checkInference(classes: Class[_]*) {
    val allClasses: Seq[Class[_]] = classes ++ classes.flatMap(_.getDeclaredClasses)
    val annotations = new MainProcessor().process(ClassSource(allClasses ++ List(classOf[Object]): _*))
    for (jClass <- allClasses; jMethod <- jClass.getDeclaredMethods) {
      val method = Method(Type.getType(jClass).getInternalName, jMethod.getName, Type.getMethodDescriptor(jMethod))
      info(s"$method")
      annotations.effects(Key(method, Out, true)).isEmpty should equal (jMethod.getAnnotation(classOf[ExpectPure]) != null)
      annotations.effects(Key(method, Out, true))(PurityAnalysis.ThisChangeQuantum) should equal (jMethod.getAnnotation(classOf[ExpectLocalEffect]) != null)

    }

    for (jClass <- allClasses; jMethod <- jClass.getDeclaredConstructors) {
      val method = Method(Type.getType(jClass).getInternalName, "<init>", Type.getConstructorDescriptor(jMethod))
      info(s"$method")
      annotations.effects(Key(method, Out, true)).isEmpty should equal (jMethod.getAnnotation(classOf[ExpectPure]) != null)
      annotations.effects(Key(method, Out, true))(PurityAnalysis.ThisChangeQuantum) should equal (jMethod.getAnnotation(classOf[ExpectLocalEffect]) != null)
    }
  }
}
