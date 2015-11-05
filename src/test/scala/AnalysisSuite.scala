package faba.test

import annotations._
import data.AnalysisData

import org.objectweb.asm._
import org.scalatest.{Matchers, FunSuite}

import faba.MainProcessor
import faba.data._
import faba.source.ClassSource

class AnalysisSuite extends FunSuite with Matchers {

  test("AnalysisData.class") {
    checkInference(classOf[AnalysisData])
  }

  def checkInference(classes: Class[_]*) {
    val annotations = new MainProcessor().process(ClassSource(classes:_*))
    for (jClass <- classes; jMethod <- jClass.getDeclaredMethods) {
      val method = Method(Type.getType(jClass).getInternalName, jMethod.getName, Type.getMethodDescriptor(jMethod))
      for {(anns, i) <- jMethod.getParameterAnnotations.zipWithIndex} {
        val notNull = anns.exists(_.annotationType == classOf[ExpectNotNull])
        assert(
          annotations.notNulls.contains(Key(method, In(i), true)) == notNull,
          s"'$jClass $jMethod #$i'"
        )
      }
      annotations.notNulls(Key(method, Out, true)) should equal (jMethod.getAnnotation(classOf[ExpectNotNull]) != null)
      annotations.contracts.get(Key(method, Out, true)) should equal (Option(jMethod.getAnnotation(classOf[ExpectContract])).map(_.value))
      info(s"$method")
    }
  }
}
