package faba.test

import annotations._
import data.InferenceWithHierarchyData

import org.objectweb.asm._
import org.scalatest.{Matchers, FunSuite}

import faba.MainProcessor
import faba.data._
import faba.source.ClassSource

// TODO - refactor test - too much repetitions for now
class InferenceWithHierarchySuite extends FunSuite with Matchers {

  test("InferenceWithHierarchyData") {
    import InferenceWithHierarchyData._
    checkInference(
      classOf[A],
      classOf[B1],
      classOf[B2],
      classOf[I],
      classOf[Impl],
      classOf[I1],
      classOf[I1Abs],
      classOf[I1Impl],
      classOf[I1AbsImpl]
    )
  }

  def checkInference(classes: Class[_]*) {
    val annotations = new MainProcessor().testProcess(ClassSource(classes:_*))
    for (jClass <- classes; jMethod <- jClass.getDeclaredMethods) {
      val method = Method(Type.getType(jClass).getInternalName, jMethod.getName, Type.getMethodDescriptor(jMethod))

      for {(anns, i) <- jMethod.getParameterAnnotations.zipWithIndex} {
        val expected = anns.exists(_.annotationType == classOf[ExpectNotNull])
        val actual = annotations.notNulls.contains(Key(method, In(i), ResolveDirection.Upward))
        val expectedString = if (expected) "@NotNull" else "null"
        val actualString = if (actual) "@NotNull" else "null"
        assert(
          actual == expected,
          s"'$jClass $jMethod #$i' expected: $expectedString, actual: $actualString"
        )

        val expectedVirtual = anns.exists(_.annotationType == classOf[ExpectVirtualNotNull])
        val actualVirtual = annotations.notNulls.contains(Key(method, In(i), ResolveDirection.Downward))
        val expectedVirtualString = if (expectedVirtual) "@VirtualNotNull" else "null"
        val actualVirtualString = if (actualVirtual) "@VirtualNotNull" else "null"
        assert(
          actualVirtual == expectedVirtual,
          s"'$jClass $jMethod #$i' expected: $expectedVirtualString, actual: $actualVirtualString"
        )
      }

      /*
      annotations.notNulls(Key(method, Out, ResolveDirection.Upward)) should equal (jMethod.getAnnotation(classOf[ExpectNotNull]) != null)
      annotations.contracts.get(Key(method, Out, ResolveDirection.Upward)) should equal (Option(jMethod.getAnnotation(classOf[ExpectContract])).map(_.value))
      */
    }
  }

}
