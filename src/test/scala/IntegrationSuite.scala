package faba.test

import java.io.File

import faba.Main
import org.scalatest.FunSuite

class IntegrationSuite extends FunSuite with IntegrationSuiteUtil {

  test("jdk7-rt.jar") {
    Main.main(
      Array("/Library/Java/JavaVirtualMachines/jdk1.7.0_80.jdk/Contents/Home/jre/lib/rt.jar", "test-results/jdk7-rt.jar")
    )
    compareOutputs(new File("results/jdk7-rt.jar"), new File("test-results/jdk7-rt.jar"))
  }

}
