package faba.test

import java.io.File

import faba.source.{JarFileSource, MixedSource}
import faba.{MainProcessor, Main}
import org.scalatest.FunSuite

class PurityIntegrationSuite extends FunSuite with IntegrationSuiteUtil {

  test("jdk7-rt.jar") {
    val jars = List("/Library/Java/JavaVirtualMachines/jdk1.7.0_80.jdk/Contents/Home/jre/lib/rt.jar")
    new MainProcessor {
      override val onlyPurityAnalysis = true
    }.process(MixedSource(jars.map {f => JarFileSource(new File(f))}), "test-results/pure-jdk7-rt.jar")
    compareOutputs(new File("results/pure-jdk7-rt.jar"), new File("test-results/pure-jdk7-rt.jar"))
  }

}
