package faba.cfg

import org.objectweb.asm.Opcodes._
import org.objectweb.asm.Type
import org.objectweb.asm.tree._
import org.objectweb.asm.tree.analysis._

import scala.collection.JavaConversions._
import scala.collection.immutable.HashSet
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object `package` {
  def buildControlFlowGraph(className: String, methodNode: MethodNode): ControlFlowGraph =
    ControlFlowBuilder(className, methodNode).buildCFG()

  def resultOrigins(className: String, methodNode: MethodNode): Set[Int] = {
    val interpreter = new MinimalOriginInterpreter
    val analyzer = new Analyzer(interpreter)
    val start = System.currentTimeMillis()
    val frames = analyzer.analyze(className, methodNode)
    val time = System.currentTimeMillis() - start
    val maxMerge = interpreter.maxMerge
    MinimalOriginInterpreter.updateMaxMerges(maxMerge)
    val mergeCount = interpreter.mergeCount
    MinimalOriginInterpreter.updateMerges(mergeCount)

    if (mergeCount > 100000) {
      System.err.println(s"$className ${methodNode.name} ${methodNode.desc} $maxMerge $time msec")
      System.err.println(s"${methodNode.instructions.size()} $mergeCount")
    }
    val insns = methodNode.instructions
    var result = Set[Int]()
    for (i <- 0 until frames.length) {
      val insnNode = insns.get(i)
      val frame = frames(i)
      if (frame != null) {
        insnNode.getOpcode match {
          case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN =>
            for (sourceInsn <- frame.pop().insns)
              result = result + insns.indexOf(sourceInsn)
          case _ =>
        }
      }
    }
    result
  }

  // the second element is a nullable leaking parameters
  def leakingParameters(className: String, methodNode: MethodNode): (Set[Int], Set[Int]) = {
    val frames = new Analyzer(new ParametersUsage(methodNode)).analyze(className, methodNode)
    val insns = methodNode.instructions
    val collector = new LeakingParametersCollector(methodNode)
    val nullableCollector = new NullableLeakingParametersCollector(methodNode)
    for (i <- 0 until frames.length) {
      val insnNode = insns.get(i)
      val frame = frames(i)
      if (frame != null) insnNode.getType match {
        case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
        case _ =>
          new Frame(frame).execute(insnNode, collector)
          new Frame(frame).execute(insnNode, nullableCollector)
      }
    }
    (collector.leaking, nullableCollector.leaking)
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

object MinimalOriginInterpreter {
  val maxMerges = new Array[Int](1000)
  val merges = new Array[Int](1000)

  def updateMaxMerges(maxMerge: Int) {
    if (maxMerge >= maxMerges.length) {
      maxMerges(maxMerges.length - 1) += 1
    } else {
      maxMerges(maxMerge) += 1
    }
  }

  def updateMerges(mergeCount: Int) {
    val count = mergeCount / 1000
    if (count >= merges.length) {
      merges(merges.length - 1) += 1
    } else {
      merges(count) += 1
    }
  }
}

class MinimalOriginInterpreter extends SourceInterpreter {
  val sourceVal1 = new SourceValue(1)
  val sourceVal2 = new SourceValue(2)
  var maxMerge = 0
  var mergeCount = 0

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

  override def merge(d: SourceValue, w: SourceValue): SourceValue = {
    val res = super.merge(d, w)
    maxMerge = math.max(maxMerge, res.insns.size())
    val size = res.insns.size()
    if (size > 2)
      mergeCount += size
    res
  }
}

case class ControlFlowGraph(className: String,
                            methodNode: MethodNode,
                            transitions: Array[List[Int]],
                            bTransitions: Array[List[Int]],
                            errorTransitions: Set[(Int, Int)])

case class RichControlFlow(controlFlow: ControlFlowGraph,
                           dfsTree: DFSTree) {

  val multiEntranceInsnIndices =
    (0 until controlFlow.transitions.length).filter(i => controlFlow.bTransitions(i).size > 1).toSet

  def isSharedInstruction(insnIndex: Int) =
    multiEntranceInsnIndices.exists(p => dfsTree.isDescendant(insnIndex, p))
}

private case class ControlFlowBuilder(className: String, methodNode: MethodNode) extends CfgAnalyzer() {
  val transitions =
    Array.tabulate[ListBuffer[Int]](methodNode.instructions.size){i => new ListBuffer()}
  val btransitions =
    Array.tabulate[ListBuffer[Int]](methodNode.instructions.size){i => new ListBuffer()}
  var errorTransitions =
    Set[(Int, Int)]()

  def buildCFG(): ControlFlowGraph = {
    if ((methodNode.access & (ACC_ABSTRACT | ACC_NATIVE)) == 0) analyze(methodNode)
    ControlFlowGraph(className, methodNode, transitions.map(_.toList), btransitions.map(_.toList), errorTransitions)
  }

  override protected def newControlFlowEdge(insn: Int, successor: Int) {
    if (!transitions(insn).contains(successor)) {
      transitions(insn) += successor
    }
    btransitions(successor) += insn
  }

  override protected def newControlFlowExceptionEdge(insn: Int, successor: Int): Boolean = {
    if (!transitions(insn).contains(successor)) {
      transitions(insn) += successor
      errorTransitions = errorTransitions + (insn -> successor)
    }
    btransitions(successor) += insn
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

case class ParamsValue(params: Set[Int], size: Int) extends Value {
  override def getSize: Int = size
}

// tracks flow of parameters into values of frame
class ParametersUsage(m: MethodNode) extends Interpreter[ParamsValue](ASM5) {
  val val1 = ParamsValue(Set(), 1)
  val val2 = ParamsValue(Set(), 2)
  var called = -1
  // the first time newValue is called for return
  // the second time (if any) for `this`
  val shift = if ((m.access & ACC_STATIC) == 0) 2 else 1
  val range = shift until (Type.getArgumentTypes(m.desc).length + shift)

  override def newValue(tp: Type): ParamsValue = {
    if (tp == null)
      return val1
    called += 1
    // hack for analyzer
    if (range.contains(called)) {
      if (tp eq Type.VOID_TYPE) null
      else if (tp.getSize == 1) ParamsValue(Set(called - shift), 1)
      else ParamsValue(Set(called - shift), 2)
    } else {
      if (tp eq Type.VOID_TYPE) null
      else if (tp.getSize == 1) val1
      else val2
    }
  }


  override def newOperation(insn: AbstractInsnNode): ParamsValue =
    insn.getOpcode match {
      case LCONST_0 | LCONST_1 | DCONST_0 | DCONST_1 =>
        val2
      case LDC =>
        val cst = insn.asInstanceOf[LdcInsnNode].cst
        if (cst.isInstanceOf[Long] || cst.isInstanceOf[Double]) val2 else val1
      case GETSTATIC =>
        if (Type.getType(insn.asInstanceOf[FieldInsnNode].desc).getSize == 1) val1 else val2
      case _ =>
        val1
    }

  override def binaryOperation(insn: AbstractInsnNode, value1: ParamsValue, value2: ParamsValue): ParamsValue =
    insn.getOpcode match {
      case LALOAD | DALOAD | LADD | DADD | LSUB | DSUB | LMUL | DMUL |
           LDIV | DDIV | LREM | LSHL | LSHR | LUSHR | LAND | LOR | LXOR =>
        val2
      case _ =>
        val1
    }

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: ParamsValue]): ParamsValue =
    insn.getOpcode match {
      case MULTIANEWARRAY =>
        val1
      case INVOKEDYNAMIC =>
        if (Type.getReturnType(insn.asInstanceOf[InvokeDynamicInsnNode].desc).getSize == 1) val1 else val2
      case _ =>
        if (Type.getReturnType(insn.asInstanceOf[MethodInsnNode].desc).getSize == 1) val1 else val2
    }

  override def unaryOperation(insn: AbstractInsnNode, value: ParamsValue): ParamsValue =
    insn.getOpcode match {
      case LNEG | DNEG | I2L | I2D | L2D | F2L | F2D | D2L =>
        val2
      case GETFIELD =>
        if (Type.getReturnType(insn.asInstanceOf[FieldInsnNode].desc).getSize == 1) val1 else val2
      case CHECKCAST =>
        ParamsValue(value.params, Type.getObjectType(insn.asInstanceOf[TypeInsnNode].desc).getSize)
      case _ =>
        val1
    }

  override def ternaryOperation(insn: AbstractInsnNode, value1: ParamsValue, value2: ParamsValue, value3: ParamsValue): ParamsValue =
    val1

  override def returnOperation(insn: AbstractInsnNode, value: ParamsValue, expected: ParamsValue): Unit = ()

  override def copyOperation(insn: AbstractInsnNode, value: ParamsValue): ParamsValue =
    value

  override def merge(v: ParamsValue, w: ParamsValue): ParamsValue = (v, w) match {
    case (_, `v`) =>
      v
    case (ParamsValue(set1, size1), ParamsValue(set2, size2)) =>
      ParamsValue(set1 ++ set2, math.min(size1, size2))
    case _ =>
      v
  }
}

class LeakingParametersCollector(m: MethodNode) extends ParametersUsage(m) {
  var leaking = Set[Int]()

  override def unaryOperation(insn: AbstractInsnNode, v: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER | INSTANCEOF | IRETURN | ARETURN |
           IFNONNULL | IFNULL | IFEQ | IFNE =>
        leaking = leaking ++ v.params
      case _ =>
    }
    super.unaryOperation(insn, v)
  }

  override def binaryOperation(insn: AbstractInsnNode, v1: ParamsValue, v2: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD | PUTFIELD =>
        leaking = leaking ++ v1.params
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  override def ternaryOperation(insn: AbstractInsnNode, v1: ParamsValue, v2: ParamsValue, v3: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE =>
        leaking = leaking ++ v1.params
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: ParamsValue]): ParamsValue = {
    insn.getOpcode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL | INVOKEINTERFACE =>
        values.foreach { v => leaking = leaking ++ v.params }
      case _ =>
    }
    super.naryOperation(insn, values)
  }

}

class NullableLeakingParametersCollector(m: MethodNode) extends LeakingParametersCollector(m) {
  override def binaryOperation(insn: AbstractInsnNode, v1: ParamsValue, v2: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case PUTFIELD =>
        leaking = leaking ++ v1.params ++ v2.params
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  override def ternaryOperation(insn: AbstractInsnNode, v1: ParamsValue, v2: ParamsValue, v3: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case AASTORE =>
        leaking = leaking ++ v1.params ++ v3.params
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

}
