name := "faba"

version := "0.1"

scalaVersion := "2.11.0"

libraryDependencies += "org.ow2.asm" % "asm-debug-all" % "5.0.1"

libraryDependencies += "org.scala-lang.modules" %% "scala-xml" % "1.0.1"

libraryDependencies += "org.scalatest" %% "scalatest" % "2.1.6" % "test"

libraryDependencies += "xmlunit" % "xmlunit" % "1.5" % "test"

scalacOptions += "-feature"

javacOptions ++= Seq("-source", "1.6")

fork := true

//javaOptions in run += "-Xmx128M"
