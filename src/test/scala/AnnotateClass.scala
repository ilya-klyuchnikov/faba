package faba.test

import faba.MainProcessor
import faba.source.ClassSource

/**
 * Test utility to annotate a class from class path
 */
object AnnotateClass {
  def main(args: Array[String]) {
    new MainProcessor().process(ClassSource(Class.forName(args(0))), args(1))
  }
}
