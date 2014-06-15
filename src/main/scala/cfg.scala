package faba.cfg

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.tree.{AbstractInsnNode, MethodNode}
import org.objectweb.asm.tree.analysis._

import scala.collection.JavaConversions._
import scala.collection.immutable.HashSet
import scala.collection.mutable

object `package` {
  def buildControlFlowGraph(className: String, methodNode: MethodNode): ControlFlowGraph =
    ControlFlowBuilder(className, methodNode).buildCFG()

  /**
   * a set (safe upper bound) of instructions where the result was born
   */
  def resultOrigins(className: String, methodNode: MethodNode): Set[Int] = {
    val frames = new Analyzer(MinimalOriginInterpreter).analyze(className, methodNode)
    val insns = methodNode.instructions
    var result = Set[Int]()
    for (i <- 0 until frames.length) {
      val insnNode = insns.get(i)
      insnNode.getOpcode match {
        case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN =>
          for (sourceInsn <- frames(i).pop().insns)
            result = result + insns.indexOf(sourceInsn)
        case _ =>
      }
    }
    result
  }

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

object MinimalOriginInterpreter extends SourceInterpreter {
  val sourceVal1 = new SourceValue(1)
  val sourceVal2 = new SourceValue(2)

  override def newOperation(insn: AbstractInsnNode): SourceValue = {
    val result = super.newOperation(insn)
    insn.getOpcode match {
      case ICONST_0 | ICONST_1 | ACONST_NULL | LDC | NEW =>
        result
      case _ =>
        new SourceValue(result.size)
    }
  }

  override def unaryOperation(insn: AbstractInsnNode, value: SourceValue) = {
    val result = super.unaryOperation(insn, value)
    insn.getOpcode match {
      case CHECKCAST | NEWARRAY | ANEWARRAY =>
        result
      case _ =>
        new SourceValue(result.size)
    }
  }

  override def binaryOperation(insn: AbstractInsnNode, value1: SourceValue, value2: SourceValue) =
    insn.getOpcode match {
      case LALOAD | DALOAD | LADD | DADD | LSUB | DSUB | LMUL | DMUL |
           LDIV | DDIV | LREM | LSHL | LSHR | LUSHR | LAND | LOR | LXOR =>
        sourceVal2
      case _ =>
        sourceVal1
    }

  override def ternaryOperation(insn: AbstractInsnNode, value1: SourceValue, value2: SourceValue, value3: SourceValue) =
    sourceVal1


  override def copyOperation(insn: AbstractInsnNode, value: SourceValue) =
    value
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
    if (!transitions(insn).contains(successor)) {
      transitions(insn) = successor :: transitions(insn)
    }
  }

  override protected def newControlFlowExceptionEdge(insn: Int, successor: Int): Boolean = {
    if (!transitions(insn).contains(successor)) {
      transitions(insn) = successor :: transitions(insn)
      errorTransitions = errorTransitions + (insn -> successor)
    }
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
