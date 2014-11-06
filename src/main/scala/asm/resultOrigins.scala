package faba.asm

import faba.analysis._

import org.objectweb.asm.tree.analysis.{Frame, SourceInterpreter, SourceValue, Value}
import org.objectweb.asm.tree.{AbstractInsnNode, IincInsnNode, MethodNode, VarInsnNode}
import org.objectweb.asm.{Opcodes, Type}

import scala.collection.mutable

/**
 * The result of origins analysis.
 *
 * @param instructions  instructions(i) means that the result was born at i-th instruction
 * @param parameters    parameters(i) means that the result may come from i-th parameter
 */
case class Origins(instructions: Array[Boolean], parameters: Array[Boolean]) {
  val instructionsMap = new Array[Int](instructions.length)
  val parametersMap = new Array[Int](parameters.length)
  // size of results
  val size: Int = {
    var shift: Int = 0
    var i: Int = 0
    val maxInsnIndex = instructions.length
    while (i < maxInsnIndex) {
      if (instructions(i)) {
        instructionsMap(i) = 1 << shift
        shift += 1
      }
      i += 1
    }
    i = 0
    val maxParam = parameters.length
    while (i < maxParam) {
      if (parameters(i)) {
        parametersMap(i) = 1 << shift
        shift += 1
      }
      i += 1
    }
    shift
  }
}

object OriginsAnalysis {

  // Values to support backward analysis
  @AsmAbstractValue case class LocalVarValue(slot: Int, _size: Int) extends SourceValue(_size, nullSet)
  @AsmAbstractValue case class OnStackValue(slot: Int, _size: Int) extends SourceValue(_size, nullSet)

  /**
   * Location of a value inside a frame
   */
  sealed trait InFrameLocation

  /**
   * Value is located in a list of local variables.
   * @param slot local variable index
   */
  case class LocalVarLocation(slot: Int) extends InFrameLocation

  /**
   * Value is located on operand stack
   * @param slot stack index
   */
  case class OnStackLocation(slot: Int) extends InFrameLocation

  /**
   * Precise value location = instruction, frame location
   * @param insnIndex instruction index
   * @param location  Inside frame location
   */
  case class PreciseValueLocation(insnIndex: Int, location: InFrameLocation)

  /**
   * Tweak of [[org.objectweb.asm.tree.analysis.SourceInterpreter]] enough for backward analysis
   */
  object TracingInterpreter extends SourceInterpreter {
    override def copyOperation(insn: AbstractInsnNode, value: SourceValue): SourceValue =
      value

    override def unaryOperation(insn: AbstractInsnNode, value: SourceValue) =
      if (insn.getOpcode == Opcodes.CHECKCAST) value
      else super.unaryOperation(insn, value)
  }

  private val nullSet: java.util.Set[AbstractInsnNode] = null

  /**
   * Detects points (parameters ans instructions) where the result of the method was born.
   * Internally this analysis executes bytecode instructions backward.
   *
   * @param frames     fixpoint of frames (after some analysis) - to know local vars and stack partition and value sizes
   * @param methodNode bytecode of a method
   * @param graph      control flow graph of a method
   * @return           result of analysis
   */
  def resultOrigins(frames: Array[Frame[Value]], methodNode: MethodNode, graph: ControlFlowGraph): Origins = {
    val shift = if ((methodNode.access & Opcodes.ACC_STATIC) != 0) 0 else 1
    val arity = Type.getArgumentTypes(methodNode.desc).length
    val insns = methodNode.instructions
    val backwardTransitions = reverseTransitions(graph.transitions)

    val queue = mutable.Stack[PreciseValueLocation]()
    val visited = mutable.HashSet[PreciseValueLocation]()

    val returnIndices = (0 until frames.length).filter { i => isReturnOpcode(insns.get(i).getOpcode)}
    for (returnIndex <- returnIndices; from <- backwardTransitions(returnIndex)) {
      // return value is on top of the stack
      val sourceLoc = PreciseValueLocation(from, OnStackLocation(frames(returnIndex).getStackSize - 1))
      visited.add(sourceLoc)
      queue.push(sourceLoc)
    }


    val originInsns = new Array[Boolean](insns.size())
    val originParams = new Array[Boolean](arity)

    while (queue.nonEmpty) {
      val PreciseValueLocation(insnIndex, location) = queue.pop()
      preLocation(insns.get(insnIndex), location, frames(insnIndex)) match {
        case None =>
          // result was born here, logging it
          originInsns(insnIndex) = true
        case Some(loc) =>
          val previousInsns = backwardTransitions(insnIndex)
          for (from <- previousInsns) {
            val insnLoc = PreciseValueLocation(from, loc)
            if (visited.add(insnLoc))
              queue.push(insnLoc)
          }
          if (previousInsns.isEmpty && insnIndex == 0) {
            loc match {
              case LocalVarLocation(i) if (i >= shift) && (i - shift < arity) =>
                // result came from some parameter, logging it
                originParams(i - shift) = true
              case _ =>
            }
          }
      }
    }

    Origins(originInsns, originParams)
  }

  /**
   * reverses forward transitions of control flow graph
   *
   * @param transitions forward transitions of control flow graph
   * @return            backward transitions
   */
  private def reverseTransitions(transitions: Array[List[Int]]): Array[List[Int]] = {
    val backTransitions: Array[List[Int]] = Array.tabulate[List[Int]](transitions.length) { i => Nil}
    for (from <- 0 until transitions.length) {
      for (to <- transitions(from)) {
        backTransitions(to) = from :: backTransitions(to)
      }
    }
    backTransitions
  }

  /**
   * One step of symbolic backward execution.
   *
   * @param insn          executed instruction
   * @param postLocation  value (in-frame) location after execution of instruction
   * @param postFrame     frame after execution of instruction
   * @return              value (in-frame) location before execution of instruction
   */
  private def preLocation(insn: AbstractInsnNode, postLocation: InFrameLocation, postFrame: Frame[Value]): Option[InFrameLocation] = {
    // optimization: instruction execution doesn't change location of our value, returning the same location
    insn.getType match {
      case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
        // idle instruction, the same location
        return Some(postLocation)
      case _ =>
    }
    postLocation match {
      case LocalVarLocation(localVar) =>
        if (!isWriteToLocalVarInsn(localVar, insn)) {
          // nothing was moved into variable, the same location
          return Some(postLocation)
        }
      case _ =>
    }

    // real analysis: backward execution
    val frame = makePreFrame(postFrame)
    frame.execute(insn, TracingInterpreter)
    // connect postLocation with executed frame
    postLocation match {
      case LocalVarLocation(slot) => valueToLocation(frame.getLocal(slot))
      case OnStackLocation(slot)  => valueToLocation(frame.getStack(slot))
      case _                      => None
    }
  }

  private def valueToLocation(value: SourceValue): Option[InFrameLocation] =
    value match {
      case LocalVarValue(sourceSlot, _) => Some(LocalVarLocation(sourceSlot))
      case OnStackValue(sourceSlot, _)  => Some(OnStackLocation(sourceSlot))
      case _                            => None
    }

  /**
   * makes a corresponding frame for backtracking
   *
   * @param frame frame with traditional values
   * @return      frame with [[LocalVarValue]]s and [[OnStackValue]]s
   */
  private def makePreFrame(frame: Frame[Value]): Frame[SourceValue] = {
    val preFrame = new Frame[SourceValue](frame.getLocals, frame.getMaxStackSize)
    for (i <- 0 until frame.getLocals) {
      preFrame.setLocal(i, LocalVarValue(i, frame.getLocal(i).getSize))
    }
    for (i <- 0 until frame.getStackSize) {
      preFrame.push(OnStackValue(i, frame.getStack(i).getSize))
    }
    preFrame
  }

  /**
   *
   * @param localVar location of a local var
   * @param insn     executed instruction
   * @return         whether executed insn writes into localVar
   */
  private def isWriteToLocalVarInsn(localVar: Int, insn: AbstractInsnNode): Boolean = {
    val opCode = insn.getOpcode
    if (opCode >= Opcodes.ISTORE && opCode <= Opcodes.ASTORE)
      return insn.asInstanceOf[VarInsnNode].`var` == localVar
    if (opCode == Opcodes.IINC)
      return insn.asInstanceOf[IincInsnNode].`var` == localVar
    false
  }

  private def isReturnOpcode(opcode: Int) =
    opcode >= Opcodes.IRETURN && opcode <= Opcodes.ARETURN

}
