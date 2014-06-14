package faba.examples

import faba.Main
import faba.source.{JarFileSource, MixedSource}
import java.io.File

object scalaJDK8 extends App {
  val jdk8Home = "/Library/Java/JavaVirtualMachines/jdk1.8.0_05.jdk/Contents/Home"
  val paths =
    List(
      s"$jdk8Home/lib/ant-javafx.jar",
      s"$jdk8Home/lib/dt.jar",
      s"$jdk8Home/lib/javafx-mx.jar",
      s"$jdk8Home/lib/jconsole.jar",
      s"$jdk8Home/lib/sa-jdi.jar",
      s"$jdk8Home/lib/tools.jar",
      s"$jdk8Home/jre/lib/charsets.jar",
      s"$jdk8Home/jre/lib/deploy.jar",
      s"$jdk8Home/jre/lib/htmlconverter.jar",
      s"$jdk8Home/jre/lib/javaws.jar",
      s"$jdk8Home/jre/lib/jce.jar",
      s"$jdk8Home/jre/lib/jfr.jar",
      s"$jdk8Home/jre/lib/jfxswt.jar",
      s"$jdk8Home/jre/lib/jsse.jar",
      s"$jdk8Home/jre/lib/management-agent.jar",
      s"$jdk8Home/jre/lib/plugin.jar",
      s"$jdk8Home/jre/lib/resources.jar",
      s"$jdk8Home/jre/lib/rt.jar",
      s"$jdk8Home/jre/lib/ext/cldrdata.jar",
      s"$jdk8Home/jre/lib/ext/dnsns.jar",
      s"$jdk8Home/jre/lib/ext/jfxrt.jar",
      s"$jdk8Home/jre/lib/ext/localedata.jar",
      s"$jdk8Home/jre/lib/ext/nashorn.jar",
      s"$jdk8Home/jre/lib/ext/sunec.jar",
      s"$jdk8Home/jre/lib/ext/sunjce_provider.jar",
      s"$jdk8Home/jre/lib/ext/sunpkcs11.jar",
      s"$jdk8Home/jre/lib/ext/zipfs.jar"
    )

  val sources = paths.map(p => JarFileSource(new File(p)))
  Main.process(MixedSource(sources), "jdk8")
}
