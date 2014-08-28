package faba.asm

import faba.cfg.ControlFlowGraph
import org.objectweb.asm.{Opcodes, Type}
import org.objectweb.asm.tree.analysis.{Frame, SourceInterpreter, SourceValue}
import org.objectweb.asm.tree.{MethodNode, AbstractInsnNode}

import scala.collection.mutable

case class Origins(instructions: Array[Boolean], parameters: Array[Boolean])

object OriginsAnalysis {
  val nullSet: java.util.Set[AbstractInsnNode] = null
  case class LocalVarValue(slot: Int, _size: Int) extends SourceValue(_size, nullSet)
  case class OnStackValue(slot: Int, _size: Int) extends SourceValue(_size, nullSet)

  sealed trait Location
  case class LocalValLocation(slot: Int) extends Location
  case class OnStackLocation(slot: Int) extends Location
  case class InsnLocation(insnIndex: Int, location: Location)

  object TracingInterpreter extends SourceInterpreter {
    override def copyOperation(insn: AbstractInsnNode, value: SourceValue): SourceValue =
      value
  }

  private def isReturnOpcode(opcode: Int) =
    opcode >= Opcodes.IRETURN && opcode <= Opcodes.ARETURN

  def resultOrigins(frames: Array[Frame[ParamsValue]], methodNode: MethodNode, graph: ControlFlowGraph): Origins = {
    val static = (methodNode.access & Opcodes.ACC_STATIC) != 0
    val shift = if (static) 0 else 1
    val arity = Type.getArgumentTypes(methodNode.desc).length
    val insns = methodNode.instructions
    val returnIndices = (0 until frames.length).filter { i => isReturnOpcode(insns.get(i).getOpcode)}.toList
    val backTransitions: Array[List[Int]] = Array.tabulate[List[Int]](insns.size){i => Nil}
    for (from <- 0 until graph.transitions.length) {
      for (to <- graph.transitions(from)) {
        backTransitions(to) = from :: backTransitions(to)
      }
    }

    val queue = mutable.Stack[InsnLocation]()
    val visited = mutable.HashSet[InsnLocation]()

    for (returnIndex <- returnIndices; returnFrame = frames(returnIndex); from <- backTransitions(returnIndex)) {
      val sourceLoc = InsnLocation(from, OnStackLocation(returnFrame.getStackSize - 1))
      visited.add(sourceLoc)
      queue.push(sourceLoc)
    }

    val originInsns = new Array[Boolean](insns.size())
    val originParams = new Array[Boolean](arity)

    while (queue.nonEmpty) {
      val resultLocation = queue.pop()
      val insnIndex = resultLocation.insnIndex
      val sourceLocation = previousLocation(frames(insnIndex), resultLocation, insns.get(insnIndex))
      sourceLocation match {
        case None =>
          // result was born here
          originInsns(insnIndex) = true
        case Some(loc) =>
          val previousInsns = backTransitions(insnIndex)
          for (from <- previousInsns) {
            val insnLoc = InsnLocation(from, loc)
            if (visited.add(insnLoc))
              queue.push(insnLoc)
          }
          if (previousInsns.isEmpty && insnIndex == 0) {
            loc match {
              case LocalValLocation(i) if (i >= shift) && (i - shift < arity) =>
                // result came from some parameter
                originParams(i - shift) = true
              case _ =>
            }
          }
      }

    }

    Origins(originInsns, originParams)
  }

  def previousLocation(postFrame: Frame[ParamsValue], result: InsnLocation, insn: AbstractInsnNode): Option[Location] = {
    insn.getType match {
      case AbstractInsnNode.LABEL | AbstractInsnNode.LINE | AbstractInsnNode.FRAME =>
        return Some(result.location)
      case _ =>
    }
    val opCode = insn.getOpcode
    result.location match {
      case LocalValLocation(_) =>
        if (!(opCode >= Opcodes.ISTORE && opCode <= Opcodes.ASTORE || opCode == Opcodes.IINC)) {
          // nothing was moved into variable, the same location
          return Some(result.location)
        }
      case _ =>
    }
    val preFrame = makePreFrame(postFrame)
    preFrame.execute(insn, TracingInterpreter)
    result.location match {
      case LocalValLocation(slot) =>
        preFrame.getLocal(slot) match {
          case LocalVarValue(sourceSlot, _) =>
            Some(LocalValLocation(sourceSlot))
          case OnStackValue(sourceSlot, _) =>
            Some(OnStackLocation(sourceSlot))
          case _ => None
        }
      case OnStackLocation(slot) =>
        preFrame.getStack(slot) match {
          case LocalVarValue(sourceSlot, _) =>
            Some(LocalValLocation(sourceSlot))
          case OnStackValue(sourceSlot, _) =>
            Some(OnStackLocation(sourceSlot))
          case _ => None
        }
      case _ =>
        None
    }
  }

  // makes a corresponding frame for backtracking
  def makePreFrame(frame: Frame[ParamsValue]): Frame[SourceValue] = {
    val preFrame = new Frame[SourceValue](frame.getLocals, frame.getMaxStackSize)
    for (i <- 0 until frame.getLocals) {
      preFrame.setLocal(i, LocalVarValue(i, frame.getLocal(i).getSize))
    }
    for (i <- 0 until frame.getStackSize) {
      preFrame.push(OnStackValue(i, frame.getStack(i).getSize))
    }
    preFrame
  }
}
