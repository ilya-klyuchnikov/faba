package faba.java

import java.io.File
import java.util.HashMap
import java.util.Map

object Main {
  def main(args: Array[String]) {
    if (args.length != 2) {
      System.out.println("Usage: faba.java.Main inputJar outDir")
    }
    else {
      new Main().process(new JarFileSource(new File(args(0))), args(1))
    }
  }

  private[java] final val valueLattice: ELattice[Value] = new ELattice[Value](Value.Bot, Value.Top)
}

class Main extends JavaProcessor {

  def process(source: Source, outDir: String) {
    val indexStart: Long = System.currentTimeMillis
    source.process(this)
    val indexEnd: Long = System.currentTimeMillis
  }
}

