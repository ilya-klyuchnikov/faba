package faba.cfg;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.*;
import org.objectweb.asm.tree.analysis.*;

import java.util.ArrayList;
import java.util.List;

public class LiteAnalyzer<V extends Value> implements Opcodes {

    private final Interpreter<V> interpreter;

    private int n;

    private InsnList insns;

    private List<TryCatchBlockNode>[] handlers;

    private Frame<V>[] frames;

    private boolean[] queued;

    private int[] queue;

    private int top;

    /**
     * Constructs a new {@link Analyzer}.
     *
     * @param interpreter
     *            the interpreter to be used to symbolically interpret the
     *            bytecode instructions.
     */
    public LiteAnalyzer(final Interpreter<V> interpreter) {
        this.interpreter = interpreter;
    }

    /**
     * Analyzes the given method.
     *
     * @param owner
     *            the internal name of the class to which the method belongs.
     * @param m
     *            the method to be analyzed.
     * @return the symbolic state of the execution stack frame at each bytecode
     *         instruction of the method. The size of the returned array is
     *         equal to the number of instructions (and labels) of the method. A
     *         given frame is <tt>null</tt> if and only if the corresponding
     *         instruction cannot be reached (dead code).
     * @throws org.objectweb.asm.tree.analysis.AnalyzerException
     *             if a problem occurs during the analysis.
     */
    public Frame<V>[] analyze(final String owner, final MethodNode m)
            throws AnalyzerException {
        if ((m.access & (ACC_ABSTRACT | ACC_NATIVE)) != 0 || m.instructions.size() == 0) {
            frames = (Frame<V>[]) new Frame<?>[0];
            return frames;
        }
        n = m.instructions.size();
        insns = m.instructions;
        handlers = (List<TryCatchBlockNode>[]) new List<?>[n];
        frames = (Frame<V>[]) new Frame<?>[n];
        queued = new boolean[n];
        queue = new int[n];
        top = 0;

        // computes exception handlers for each instruction
        for (int i = 0; i < m.tryCatchBlocks.size(); ++i) {
            TryCatchBlockNode tcb = m.tryCatchBlocks.get(i);
            int begin = insns.indexOf(tcb.start);
            int end = insns.indexOf(tcb.end);
            for (int j = begin; j < end; ++j) {
                List<TryCatchBlockNode> insnHandlers = handlers[j];
                if (insnHandlers == null) {
                    insnHandlers = new ArrayList<TryCatchBlockNode>();
                    handlers[j] = insnHandlers;
                }
                insnHandlers.add(tcb);
            }
        }

        // initializes the data structures for the control flow analysis
        Frame<V> current = newFrame(m.maxLocals, m.maxStack);
        Frame<V> handler = newFrame(m.maxLocals, m.maxStack);
        current.setReturn(interpreter.newValue(Type.getReturnType(m.desc)));
        Type[] args = Type.getArgumentTypes(m.desc);
        int local = 0;
        if ((m.access & ACC_STATIC) == 0) {
            Type ctype = Type.getObjectType(owner);
            current.setLocal(local++, interpreter.newValue(ctype));
        }
        for (int i = 0; i < args.length; ++i) {
            current.setLocal(local++, interpreter.newValue(args[i]));
            if (args[i].getSize() == 2) {
                current.setLocal(local++, interpreter.newValue(null));
            }
        }
        while (local < m.maxLocals) {
            current.setLocal(local++, interpreter.newValue(null));
        }
        merge(0, current);

        init(owner, m);

        // control flow analysis
        while (top > 0) {
            int insn = queue[--top];
            Frame<V> f = frames[insn];
            queued[insn] = false;

            AbstractInsnNode insnNode = null;
            try {
                insnNode = m.instructions.get(insn);
                int insnOpcode = insnNode.getOpcode();
                int insnType = insnNode.getType();

                if (insnType == AbstractInsnNode.LABEL
                        || insnType == AbstractInsnNode.LINE
                        || insnType == AbstractInsnNode.FRAME) {
                    merge(insn + 1, f);
                    newControlFlowEdge(insn, insn + 1);
                } else {
                    current.init(f).execute(insnNode, interpreter);

                    if (insnNode instanceof JumpInsnNode) {
                        JumpInsnNode j = (JumpInsnNode) insnNode;
                        if (insnOpcode != GOTO && insnOpcode != JSR) {
                            merge(insn + 1, current);
                            newControlFlowEdge(insn, insn + 1);
                        }
                        int jump = insns.indexOf(j.label);
                        merge(jump, current);
                        newControlFlowEdge(insn, jump);
                    } else if (insnNode instanceof LookupSwitchInsnNode) {
                        LookupSwitchInsnNode lsi = (LookupSwitchInsnNode) insnNode;
                        int jump = insns.indexOf(lsi.dflt);
                        merge(jump, current);
                        newControlFlowEdge(insn, jump);
                        for (int j = 0; j < lsi.labels.size(); ++j) {
                            LabelNode label = lsi.labels.get(j);
                            jump = insns.indexOf(label);
                            merge(jump, current);
                            newControlFlowEdge(insn, jump);
                        }
                    } else if (insnNode instanceof TableSwitchInsnNode) {
                        TableSwitchInsnNode tsi = (TableSwitchInsnNode) insnNode;
                        int jump = insns.indexOf(tsi.dflt);
                        merge(jump, current);
                        newControlFlowEdge(insn, jump);
                        for (int j = 0; j < tsi.labels.size(); ++j) {
                            LabelNode label = tsi.labels.get(j);
                            jump = insns.indexOf(label);
                            merge(jump, current);
                            newControlFlowEdge(insn, jump);
                        }
                    } else if (insnOpcode != ATHROW
                            && (insnOpcode < IRETURN || insnOpcode > RETURN)) {
                        merge(insn + 1, current);
                        newControlFlowEdge(insn, insn + 1);
                    }
                }

                List<TryCatchBlockNode> insnHandlers = handlers[insn];
                if (insnHandlers != null) {
                    for (int i = 0; i < insnHandlers.size(); ++i) {
                        TryCatchBlockNode tcb = insnHandlers.get(i);
                        Type type;
                        if (tcb.type == null) {
                            type = Type.getObjectType("java/lang/Throwable");
                        } else {
                            type = Type.getObjectType(tcb.type);
                        }
                        int jump = insns.indexOf(tcb.handler);
                        if (newControlFlowExceptionEdge(insn, tcb)) {
                            handler.init(f);
                            handler.clearStack();
                            handler.push(interpreter.newValue(type));
                            merge(jump, handler);
                        }
                    }
                }
            } catch (AnalyzerException e) {
                throw new AnalyzerException(e.node, "Error at instruction "  + insn + ": " + e.getMessage(), e);
            } catch (Exception e) {
                throw new AnalyzerException(insnNode, "Error at instruction " + insn + ": " + e.getMessage(), e);
            }
        }

        return frames;
    }

    /**
     * Returns the symbolic stack frame for each instruction of the last
     * recently analyzed method.
     *
     * @return the symbolic state of the execution stack frame at each bytecode
     *         instruction of the method. The size of the returned array is
     *         equal to the number of instructions (and labels) of the method. A
     *         given frame is <tt>null</tt> if the corresponding instruction
     *         cannot be reached, or if an error occured during the analysis of
     *         the method.
     */
    public Frame<V>[] getFrames() {
        return frames;
    }

    /**
     * Returns the exception handlers for the given instruction.
     *
     * @param insn
     *            the index of an instruction of the last recently analyzed
     *            method.
     * @return a list of {@link TryCatchBlockNode} objects.
     */
    public List<TryCatchBlockNode> getHandlers(final int insn) {
        return handlers[insn];
    }

    /**
     * Initializes this analyzer. This method is called just before the
     * execution of control flow analysis loop in #analyze. The default
     * implementation of this method does nothing.
     *
     * @param owner
     *            the internal name of the class to which the method belongs.
     * @param m
     *            the method to be analyzed.
     * @throws AnalyzerException
     *             if a problem occurs.
     */
    protected void init(String owner, MethodNode m) throws AnalyzerException {
    }

    /**
     * Constructs a new frame with the given size.
     *
     * @param nLocals
     *            the maximum number of local variables of the frame.
     * @param nStack
     *            the maximum stack size of the frame.
     * @return the created frame.
     */
    protected Frame<V> newFrame(final int nLocals, final int nStack) {
        return new Frame<V>(nLocals, nStack);
    }

    /**
     * Constructs a new frame that is identical to the given frame.
     *
     * @param src
     *            a frame.
     * @return the created frame.
     */
    protected Frame<V> newFrame(final Frame<? extends V> src) {
        return new Frame<V>(src);
    }

    /**
     * Creates a control flow graph edge. The default implementation of this
     * method does nothing. It can be overriden in order to construct the
     * control flow graph of a method (this method is called by the
     * {@link #analyze analyze} method during its visit of the method's code).
     *
     * @param insn
     *            an instruction index.
     * @param successor
     *            index of a successor instruction.
     */
    protected void newControlFlowEdge(final int insn, final int successor) {
    }

    /**
     * Creates a control flow graph edge corresponding to an exception handler.
     * The default implementation of this method does nothing. It can be
     * overridden in order to construct the control flow graph of a method (this
     * method is called by the {@link #analyze analyze} method during its visit
     * of the method's code).
     *
     * @param insn
     *            an instruction index.
     * @param successor
     *            index of a successor instruction.
     * @return true if this edge must be considered in the data flow analysis
     *         performed by this analyzer, or false otherwise. The default
     *         implementation of this method always returns true.
     */
    protected boolean newControlFlowExceptionEdge(final int insn,
                                                  final int successor) {
        return true;
    }

    /**
     * Creates a control flow graph edge corresponding to an exception handler.
     * The default implementation of this method delegates to
     * {@link #newControlFlowExceptionEdge(int, int)
     * newControlFlowExceptionEdge(int, int)}. It can be overridden in order to
     * construct the control flow graph of a method (this method is called by
     * the {@link #analyze analyze} method during its visit of the method's
     * code).
     *
     * @param insn
     *            an instruction index.
     * @param tcb
     *            TryCatchBlockNode corresponding to this edge.
     * @return true if this edge must be considered in the data flow analysis
     *         performed by this analyzer, or false otherwise. The default
     *         implementation of this method delegates to
     *         {@link #newControlFlowExceptionEdge(int, int)
     *         newControlFlowExceptionEdge(int, int)}.
     */
    protected boolean newControlFlowExceptionEdge(final int insn,
                                                  final TryCatchBlockNode tcb) {
        return newControlFlowExceptionEdge(insn, insns.indexOf(tcb.handler));
    }

    private void merge(final int insn, final Frame<V> frame) throws AnalyzerException {
        Frame<V> oldFrame = frames[insn];
        boolean changes;

        if (oldFrame == null) {
            frames[insn] = newFrame(frame);
            changes = true;
        } else {
            changes = oldFrame.merge(frame, interpreter);
        }
        if (changes && !queued[insn]) {
            queued[insn] = true;
            queue[top++] = insn;
        }
    }

}

