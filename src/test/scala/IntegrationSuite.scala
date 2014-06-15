package faba.test

import java.io.File
import javax.xml.parsers.DocumentBuilderFactory

import faba.Main
import org.custommonkey.xmlunit.Diff
import org.scalatest.FunSuite

class IntegrationSuite extends FunSuite {

  test("jdk7-rt.jar") {
    Main.main(
      Array("/Library/Java/JavaVirtualMachines/jdk1.7.0_45.jdk/Contents/Home/jre/lib/rt.jar", "test-results/jdk7-rt.jar")
    )
    compareOutputs(new File("results/jdk7-rt.jar"), new File("test-results/jdk7-rt.jar"))
  }

  def compareOutputs(dir1: File, dir2: File) {
    val paths = annotationXmlPaths(dir1).toSet.toList.sorted
    val actualPaths = annotationXmlPaths(dir2).toSet.toList.sorted
    assert(paths == actualPaths)
    paths.foreach {p => compareXMLs(new File(dir1, p), new File(dir2, p))}
  }

  def annotationXmlPaths(dir: File): Array[String] = {
    def getRelativePath(dir: File, file: File) =
      file.getAbsolutePath.substring(dir.getAbsolutePath.length() + 1)
    def listFiles(f: File): Array[File] = {
      val these = f.listFiles
      these.filterNot(_.isDirectory) ++ these.filter(_.isDirectory).flatMap(listFiles)
    }
    listFiles(dir).filter(_.getName == "annotations.xml").map(getRelativePath(dir, _))
  }

  def compareXMLs(f1: File, f2: File) {
    val builder = DocumentBuilderFactory.newInstance().newDocumentBuilder()
    val diff = new Diff(builder.parse(f1), builder.parse(f2))
    assert(diff.similar(), s"files ${f1.getAbsolutePath} and ${f2.getAbsolutePath} have different content")
  }
}
