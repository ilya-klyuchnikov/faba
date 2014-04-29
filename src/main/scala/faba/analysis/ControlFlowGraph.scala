package faba.analysis

import org.objectweb.asm.tree.MethodNode
import org.objectweb.asm.tree.analysis.{BasicInterpreter, Analyzer}

/**
 * Control flow graph specialized for bytecode
 *
 * @param className - internal class name
 * @param methodNode - method node corresponding to this CFG
 * @param transitions - all transitions
 * @param errorTransitions - marker set for error transitions
 */
case class ControlFlowGraph(className: String,
                            methodNode: MethodNode,
                            transitions: Array[List[Int]],
                            errorTransitions: Set[(Int, Int)])


case class RichControlFlow(controlFlow: ControlFlowGraph,
                           dfsTree: DFSTree)

object ControlFlowGraph {
  def buildControlFlowGraph(className: String, methodNode: MethodNode): ControlFlowGraph =
    ControlFlowBuilder(className, methodNode).buildCFG()

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
}
