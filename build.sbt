name := "faba"

version := "1.1.0-SNAPSHOT"

scalaVersion := "2.11.4"

libraryDependencies += "org.ow2.asm" % "asm-debug-all" % "5.0.3"

libraryDependencies += "org.scala-lang.modules" %% "scala-xml" % "1.0.2"

libraryDependencies += "org.scalatest" %% "scalatest" % "2.2.1" % "test"

libraryDependencies += "xmlunit" % "xmlunit" % "1.5" % "test"

scalacOptions += "-feature"

scalacOptions += "-Yinline-warnings"

fork := true

//javaOptions in run += "-Xmx128M"
