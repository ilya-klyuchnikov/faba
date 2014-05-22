package faba.cfg

import scala.collection.immutable.HashSet
import scala.collection.mutable

import org.objectweb.asm.tree.MethodNode
import org.objectweb.asm.tree.analysis.{BasicInterpreter, Analyzer}

object `package` {
  def buildControlFlowGraph(className: String, methodNode: MethodNode): ControlFlowGraph =
    ControlFlowBuilder(className, methodNode).buildCFG()

  // Graphs: Theory and Algorithms. by K. Thulasiraman , M. N. S. Swamy (1992)
  // 11.7.2 DFS of a directed graph
  def buildDFSTree(transitions: Array[List[Int]]): DFSTree = {
    type Edge = (Int, Int)

    sealed trait Action
    case class MarkScanned(node: Int) extends Action
    case class ExamineEdge(from: Int, to: Int) extends Action

    var tree, forward, back, cross = HashSet[Edge]()
    // marked = entered
    val marked = new Array[Boolean](transitions.length)
    val scanned = new Array[Boolean](transitions.length)
    val preOrder = new Array[Int](transitions.length)
    val postOrder = new Array[Int](transitions.length)

    var entered = 0
    var completed = 0
    val stack = scala.collection.mutable.Stack[Action]()
    var loopEnters = HashSet[Int]()

    @inline
    def enter(n: Int): Unit = {
      entered += 1
      preOrder(n) = entered
      marked(n) = true
      stack.push(MarkScanned(n))
      stack.pushAll(transitions(n).map(ExamineEdge(n, _)))
    }

    // entering
    enter(0)

    while (stack.nonEmpty) {
      val action = stack.pop()
      action match {
        case MarkScanned(n) =>
          completed += 1
          postOrder(n) = completed
          scanned(n) = true
        case ExamineEdge(from, to) =>
          if (!marked(to)) {
            enter(to)
            tree = tree + (from -> to)
          } else if (preOrder(to) > preOrder(from)) {
            forward = forward + (from -> to)
          } else if (preOrder(to) < preOrder(from) && !scanned(to)) {
            back = back + (from -> to)
            loopEnters = loopEnters + to
          } else {
            cross = cross + (from -> to)
          }
      }
    }

    DFSTree(preOrder, postOrder, tree, forward, back, cross, loopEnters)
  }

  // Tarjan. Testing flow graph reducibility.
  // Journal of Computer and System Sciences 9.3 (1974): 355-365.
  def reducible(cfg: ControlFlowGraph, dfs: DFSTree): Boolean = {
    val size = cfg.transitions.length

    val cycles2Node = Array.tabulate(size){i => mutable.HashSet[Int]()}
    val nonCycles2Node = Array.tabulate(size){i => mutable.HashSet[Int]()}
    val collapsedTo = Array.tabulate[Int](size)(i => i)

    for ((from, to) <- dfs.back) cycles2Node(to).add(from)
    for ((from, to) <- dfs.tree) nonCycles2Node(to).add(from)
    for ((from, to) <- dfs.forward) nonCycles2Node(to).add(from)
    for ((from, to) <- dfs.cross) nonCycles2Node(to).add(from)

    for (w <- (size - 1) to 0 by -1) {
      val seq: Seq[Int] = cycles2Node(w).toSeq
      val p = mutable.HashSet[Int](seq:_*)
      val queue = mutable.Queue[Int](seq:_*)

      while(queue.nonEmpty) {
        val x = queue.dequeue()
        for (y <- nonCycles2Node(x)) {
          val y1 = collapsedTo(y)
          if (!dfs.isDescendant(y1, w)) return false
          if (y1 != w && p.add(y1)) queue.enqueue(y1)
        }
      }

      for (x <- p) collapsedTo(x) = w

    }

    true
  }
}

case class ControlFlowGraph(className: String,
                            methodNode: MethodNode,
                            transitions: Array[List[Int]],
                            errorTransitions: Set[(Int, Int)])

case class RichControlFlow(controlFlow: ControlFlowGraph,
                           dfsTree: DFSTree)

private case class ControlFlowBuilder(className: String,
                                      methodNode: MethodNode) extends Analyzer(new BasicInterpreter()) {
  val transitions =
    Array.tabulate[List[Int]](methodNode.instructions.size){i => Nil}
  var errorTransitions =
    Set[(Int, Int)]()

  def buildCFG(): ControlFlowGraph = {
    analyze(className, methodNode)
    ControlFlowGraph(className, methodNode, transitions, errorTransitions)
  }

  override protected def newControlFlowEdge(insn: Int, successor: Int) {
    transitions(insn) = successor :: transitions(insn)
  }

  override protected def newControlFlowExceptionEdge(insn: Int, successor: Int): Boolean = {
    transitions(insn) = successor :: transitions(insn)
    errorTransitions = errorTransitions + (insn -> successor)
    true
  }
}


case class DFSTree(preOrder: Array[Int],
                   postOrder: Array[Int],
                   tree: Set[(Int, Int)],
                   forward: Set[(Int, Int)],
                   back: Set[(Int, Int)],
                   cross: Set[(Int, Int)],
                   loopEnters: Set[Int]) {

  def isDescendant(child: Int, parent: Int): Boolean =
    preOrder(parent) <= preOrder(child) && postOrder(child) <= postOrder(parent)

}
