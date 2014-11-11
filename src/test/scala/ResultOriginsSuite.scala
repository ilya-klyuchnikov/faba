package faba.test

import annotations._
import data.ResultOriginsData
import faba.analysis.leakingParameters._
import faba.analysis.resultOrigins.OriginsAnalysis
import faba.data._
import org.objectweb.asm._
import org.objectweb.asm.tree.MethodNode
import org.objectweb.asm.tree.analysis.{Frame, Value => ASMValue}
import org.scalatest.{FunSuite, Matchers}

class ResultOriginsSuite extends FunSuite with Matchers {

  test("LeakingParametersData.class") {
    checkLeakingParameters(classOf[ResultOriginsData])
  }

  def checkLeakingParameters(classes: Class[_]*) {
    var map = Map[Method, Array[Boolean]]()

    // collecting result origins
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
              val controlFlowGraph = faba.analysis.controlFlow.buildControlFlowGraph(classReader.getClassName, node, jsr = false)
              val leakingParameters = LeakingParameters.build(classReader.getClassName, node, jsr = false)
              val resultOrigins = OriginsAnalysis.resultOrigins(leakingParameters.frames.asInstanceOf[Array[Frame[ASMValue]]], node, controlFlowGraph)
              info(s"$method ${resultOrigins.parameters.mkString(", ")}")
              map = map + (method -> resultOrigins.parameters)
            }
          }
        }
      }, ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES)
    }

    // checking resultOrigins parameters
    for (jClass <- classes; jMethod <- jClass.getDeclaredMethods) {
      val method = Method(Type.getType(jClass).getInternalName, jMethod.getName, Type.getMethodDescriptor(jMethod))
      for {(anns, i) <- jMethod.getParameterAnnotations.zipWithIndex} {
        val isExpectedResultOrigin = anns.exists(_.annotationType == classOf[ExpectResultOrigin])
        assert(
          map(method)(i) == isExpectedResultOrigin,
          s"'$jClass $jMethod #$i'"
        )
      }
    }
  }
}
