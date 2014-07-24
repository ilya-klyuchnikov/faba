package faba.examples

import faba.MainProcessor
import faba.source.{JarFileSource, MixedSource}
import java.io.File

object IdeaTestAnnotations extends App {
  val paths =
    List("data/mockjdk7-rt.jar","data/velocity.jar")

  val sources = paths.map(p => JarFileSource(new File(p)))
  new MainProcessor {
    override val processNullableParameters = false
  }.process(MixedSource(sources), "results/IDEA")
}
