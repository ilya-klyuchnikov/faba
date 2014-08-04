package faba.cfg

import java.util

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

  def resultOrigins(className: String, methodNode: MethodNode): Array[Boolean] = {
    val returnType = Type.getReturnType(methodNode.desc)
    val interpreter = if (Utils.isReferenceType(returnType)) ReferenceOriginInterpreter else MinimalOriginInterpreter
    val frames = new LiteAnalyzer(interpreter).analyze(className, methodNode)
    val insns = methodNode.instructions
    val result = new Array[Boolean](insns.size())
    for (i <- 0 until frames.length) {
      val insnNode = insns.get(i)
      val frame = frames(i)
      if (frame != null) {
        insnNode.getOpcode match {
          case ARETURN | IRETURN | LRETURN | FRETURN | DRETURN =>
            for (sourceInsn <- frame.pop().insns)
              result(insns.indexOf(sourceInsn)) = true
          case _ =>
        }
      }
    }
    result
  }

  // the second element is a nullable leaking parameters
  def leakingParameters(className: String, methodNode: MethodNode): (Array[Boolean], Array[Boolean]) = {
    val frames = new LiteAnalyzer(new ParametersUsage(methodNode)).analyze(className, methodNode)
    val arity = Type.getArgumentTypes(methodNode.desc).length
    val leaking1 = new Array[Boolean](arity)
    val leaking2 = new Array[Boolean](arity)
    val insns = methodNode.instructions
    val collector = new LeakingParametersCollector(methodNode, leaking1)
    val nullableCollector = new NullableLeakingParametersCollector(methodNode, leaking2)
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
    (leaking1, leaking2)
  }

  // Graphs: Theory and Algorithms. by K. Thulasiraman , M. N. S. Swamy (1992)
  // 11.7.2 DFS of a directed graph
  def buildDFSTree(transitions: Array[List[Int]]): DFSTree = {
    type Edge = (Int, Int)

    sealed trait Action
    case class MarkScanned(node: Int) extends Action
    case class ExamineEdge(from: Int, to: Int) extends Action

    var nonBack, back = HashSet[Edge]()
    // marked = entered
    val marked = new Array[Boolean](transitions.length)
    val scanned = new Array[Boolean](transitions.length)
    val preOrder = new Array[Int](transitions.length)
    val postOrder = new Array[Int](transitions.length)

    var entered = 0
    var completed = 0
    val stack = scala.collection.mutable.Stack[Action]()
    val loopEnters = new Array[Boolean](transitions.length)

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

    // back maybe only to one instruction
    // tree
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
            nonBack = nonBack + (from -> to)
          } else if (preOrder(to) > preOrder(from)) {
            nonBack = nonBack + (from -> to)
          } else if (preOrder(to) < preOrder(from) && !scanned(to)) {
            back = back + (from -> to)
            loopEnters(to) = true
          } else {
            nonBack = nonBack + (from -> to)
          }
      }
    }

    DFSTree(preOrder, postOrder, nonBack, back, loopEnters)
  }

  // Tarjan. Testing flow graph reducibility.
  // Journal of Computer and System Sciences 9.3 (1974): 355-365.
  def reducible(cfg: ControlFlowGraph, dfs: DFSTree): Boolean = {
    val size = cfg.transitions.length

    val cycles2Node = Array.tabulate(size){i => mutable.HashSet[Int]()}
    val nonCycles2Node = Array.tabulate(size){i => mutable.HashSet[Int]()}
    val collapsedTo = Array.tabulate[Int](size)(i => i)

    for ((from, to) <- dfs.back) cycles2Node(to).add(from)
    for ((from, to) <- dfs.nonBack) nonCycles2Node(to).add(from)

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

object Utils {
  def isReferenceType(tp: Type): Boolean = {
    val sort = tp.getSort
    sort == Type.OBJECT || sort == Type.ARRAY
  }

  def isBooleanType(tp: Type): Boolean = {
    Type.BOOLEAN_TYPE == tp
  }
}

// really this is just for booleans
object MinimalOriginInterpreter extends SourceInterpreter {
  val sourceVal1 = new SourceValue(1)
  val sourceVal2 = new SourceValue(2)

  override def newOperation(insn: AbstractInsnNode): SourceValue = {
    val result = super.newOperation(insn)
    insn.getOpcode match {
      // see the type of result
      case ICONST_0 | ICONST_1 =>
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

  final override def naryOperation(insn: AbstractInsnNode, values: util.List[_ <: SourceValue]): SourceValue = {
    val opCode = insn.getOpcode
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL =>
        val mNode = insn.asInstanceOf[MethodInsnNode]
        val retType = Type.getReturnType(mNode.desc)
        if (retType == Type.BOOLEAN_TYPE)
          new SourceValue(1, insn)
        else
          if (retType.getSize == 1) sourceVal1 else sourceVal2
      case INVOKEINTERFACE =>
        val mNode = insn.asInstanceOf[MethodInsnNode]
        val retType = Type.getReturnType(mNode.desc)
        if (retType.getSize == 1) sourceVal1 else sourceVal2
      case MULTIANEWARRAY =>
        sourceVal1
      case _ =>
        val mNode = insn.asInstanceOf[InvokeDynamicInsnNode]
        val retType = Type.getReturnType(mNode.desc)
        if (retType.getSize == 1) sourceVal1 else sourceVal2
    }
  }

  override def copyOperation(insn: AbstractInsnNode, value: SourceValue) =
    value
}

object ReferenceOriginInterpreter extends SourceInterpreter {
  val sourceVal1 = new SourceValue(1)
  val sourceVal2 = new SourceValue(2)

  override def newOperation(insn: AbstractInsnNode): SourceValue = {
    val result = super.newOperation(insn)
    insn.getOpcode match {
      case ACONST_NULL | LDC | NEW =>
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


  final override def naryOperation(insn: AbstractInsnNode, values: util.List[_ <: SourceValue]): SourceValue = {
    val opCode = insn.getOpcode
    opCode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL =>
        val mNode = insn.asInstanceOf[MethodInsnNode]
        val retType = Type.getReturnType(mNode.desc)
        val isRefRetType = retType.getSort == Type.OBJECT || retType.getSort == Type.ARRAY
        if (isRefRetType)
          new SourceValue(1, insn)
        else
          if (retType.getSize == 1) sourceVal1 else sourceVal2
      case INVOKEINTERFACE =>
        val mNode = insn.asInstanceOf[MethodInsnNode]
        val retType = Type.getReturnType(mNode.desc)
        if (retType.getSize == 1) sourceVal1 else sourceVal2
      case MULTIANEWARRAY =>
        new SourceValue(1, insn)
      case _ =>
        val mNode = insn.asInstanceOf[InvokeDynamicInsnNode]
        val retType = Type.getReturnType(mNode.desc)
        if (retType.getSize == 1) sourceVal1 else sourceVal2
    }
  }

  override def ternaryOperation(insn: AbstractInsnNode, value1: SourceValue, value2: SourceValue, value3: SourceValue) =
    sourceVal1


  override def copyOperation(insn: AbstractInsnNode, value: SourceValue) =
    value
}

case class ControlFlowGraph(className: String,
                            methodNode: MethodNode,
                            transitions: Array[List[Int]],
                            errorTransitions: Set[(Int, Int)],
                            errors: Array[Boolean])

case class RichControlFlow(controlFlow: ControlFlowGraph, dfsTree: DFSTree)

private case class ControlFlowBuilder(className: String, methodNode: MethodNode) extends CfgAnalyzer() {
  val transitions =
    Array.tabulate[ListBuffer[Int]](methodNode.instructions.size){i => new ListBuffer()}
  val errors =
    new Array[Boolean](methodNode.instructions.size())
  var errorTransitions =
    Set[(Int, Int)]()

  def buildCFG(): ControlFlowGraph = {
    if ((methodNode.access & (ACC_ABSTRACT | ACC_NATIVE)) == 0) analyze(methodNode)
    ControlFlowGraph(className, methodNode, transitions.map(_.toList), errorTransitions, errors)
  }

  override protected def newControlFlowEdge(insn: Int, successor: Int) {
    if (!transitions(insn).contains(successor)) {
      transitions(insn) += successor
    }
  }

  override protected def newControlFlowExceptionEdge(insn: Int, successor: Int) {
    if (!transitions(insn).contains(successor)) {
      transitions(insn) += successor
      errorTransitions = errorTransitions + (insn -> successor)
      errors(successor) = true
    }
  }
}


case class DFSTree(preOrder: Array[Int],
                   postOrder: Array[Int],
                   nonBack: Set[(Int, Int)],
                   back: Set[(Int, Int)],
                   loopEnters: Array[Boolean]) {

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
      if (tp eq Type.VOID_TYPE) return null
      if (Utils.isReferenceType(tp) || Utils.isBooleanType(tp)) {
        if (tp.getSize == 1) ParamsValue(Set(called - shift), 1)
        else ParamsValue(Set(called - shift), 2)
      } else {
        // we are not interested in such parameters
        if (tp.getSize == 1) val1 else val2
      }
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

class LeakingParametersCollector(m: MethodNode, val leaking: Array[Boolean]) extends ParametersUsage(m) {

  override def unaryOperation(insn: AbstractInsnNode, v: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case GETFIELD | ARRAYLENGTH | MONITORENTER | INSTANCEOF | IRETURN | ARETURN |
           IFNONNULL | IFNULL | IFEQ | IFNE =>
        for (i <- v.params) {
          leaking(i) = true
        }
      case _ =>
    }
    super.unaryOperation(insn, v)
  }

  override def binaryOperation(insn: AbstractInsnNode, v1: ParamsValue, v2: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case IALOAD | LALOAD | FALOAD | DALOAD | AALOAD | BALOAD | CALOAD | SALOAD | PUTFIELD =>
        for (i <- v1.params) {
          leaking(i) = true
        }
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  override def ternaryOperation(insn: AbstractInsnNode, v1: ParamsValue, v2: ParamsValue, v3: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case IASTORE | LASTORE | FASTORE | DASTORE | AASTORE | BASTORE | CASTORE | SASTORE =>
        for (i <- v1.params) {
          leaking(i) = true
        }
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

  override def naryOperation(insn: AbstractInsnNode, values: java.util.List[_ <: ParamsValue]): ParamsValue = {
    insn.getOpcode match {
      case INVOKESTATIC | INVOKESPECIAL | INVOKEVIRTUAL | INVOKEINTERFACE =>
        for (v <- values; i <- v.params) {
          leaking(i) = true
        }
      case _ =>
    }
    super.naryOperation(insn, values)
  }

}

class NullableLeakingParametersCollector(m: MethodNode, leaking: Array[Boolean]) extends LeakingParametersCollector(m, leaking) {
  override def binaryOperation(insn: AbstractInsnNode, v1: ParamsValue, v2: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case PUTFIELD =>
        for (i <- v1.params) {
          leaking(i) = true
        }
        for (i <- v2.params) {
          leaking(i) = true
        }
      case _ =>
    }
    super.binaryOperation(insn, v1, v2)
  }

  override def ternaryOperation(insn: AbstractInsnNode, v1: ParamsValue, v2: ParamsValue, v3: ParamsValue): ParamsValue = {
    insn.getOpcode match {
      case AASTORE =>
        for (i <- v1.params) {
          leaking(i) = true
        }
        for (i <- v3.params) {
          leaking(i) = true
        }
      case _ =>
    }
    super.ternaryOperation(insn, v1, v2, v3)
  }

}
