package faba.test

import annotations._
import data.Data02
import faba.asm.LeakingParameters
import faba.data._
import org.objectweb.asm._
import org.objectweb.asm.tree.MethodNode
import org.scalatest.{FunSuite, Matchers}

class LeakingParametersSuite extends FunSuite with Matchers {

  test("Data02.class") {
    checkLeakingParameters(classOf[Data02])
  }

  def checkLeakingParameters(classes: Class[_]*) {
    var map = Map[Method, Array[Boolean]]()

    // collecting leakedParameters
    for (jClass <- classes) {
      val classReader = new ClassReader(jClass.getCanonicalName)
      classReader.accept(new ClassVisitor(Opcodes.ASM5) {
        override def visit(version: Int, access: Int, name: String, signature: String, superName: String, interfaces: Array[String]) {
          super.visit(version, access, name, signature, superName, interfaces)
        }

        override def visitMethod(access: Int, name: String, desc: String, signature: String, exceptions: Array[String]) = {
          val node = new MethodNode(Opcodes.ASM5, access, name, desc, signature, exceptions)
          val method = Method(classReader.getClassName, name, desc)
          new MethodVisitor(Opcodes.ASM5, node) {
            override def visitEnd(): Unit = {
              super.visitEnd()
              val LeakingParameters(_, leaked, _) = LeakingParameters.build(classReader.getClassName, node, jsr = false)
              info(s"$method $leaked")
              map = map + (method -> leaked)
            }
          }
        }
      }, ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES)
    }

    // checking leakedParameters
    for (jClass <- classes; jMethod <- jClass.getDeclaredMethods) {
      val method = Method(Type.getType(jClass).getInternalName, jMethod.getName, Type.getMethodDescriptor(jMethod))
      for {(anns, i) <- jMethod.getParameterAnnotations.zipWithIndex} {
        val isLeaked = anns.exists(_.annotationType == classOf[ExpectLeaking])
        assert(
          map(method)(i) == isLeaked,
          s"'$jClass $jMethod #$i'"
        )
      }
    }
  }
}
