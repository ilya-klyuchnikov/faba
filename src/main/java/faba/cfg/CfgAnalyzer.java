package faba.cfg;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.*;
import org.objectweb.asm.tree.analysis.AnalyzerException;

import java.util.ArrayList;
import java.util.List;

public class CfgAnalyzer implements Opcodes {

    private InsnList insns;
    private boolean[] wasQueued;
    private boolean[] queued;
    private int[] queue;
    private int top;

    public void analyze(final MethodNode m) throws AnalyzerException {
        int n = m.instructions.size();
        insns = m.instructions;
        List<TryCatchBlockNode>[] handlers = (List<TryCatchBlockNode>[]) new List<?>[n];
        queued = new boolean[n];
        wasQueued = new boolean[n];
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

        merge(0);
        // control flow analysis
        while (top > 0) {
            int insn = queue[--top];
            queued[insn] = false;

            AbstractInsnNode insnNode = null;
            try {
                insnNode = m.instructions.get(insn);
                int insnOpcode = insnNode.getOpcode();
                int insnType = insnNode.getType();

                if (insnType == AbstractInsnNode.LABEL || insnType == AbstractInsnNode.LINE || insnType == AbstractInsnNode.FRAME) {
                    merge(insn + 1);
                    newControlFlowEdge(insn, insn + 1);
                } else {
                    if (insnNode instanceof JumpInsnNode) {
                        JumpInsnNode j = (JumpInsnNode) insnNode;
                        if (insnOpcode != GOTO && insnOpcode != JSR) {
                            merge(insn + 1);
                            newControlFlowEdge(insn, insn + 1);
                        }
                        int jump = insns.indexOf(j.label);
                        merge(jump);
                        newControlFlowEdge(insn, jump);
                    } else if (insnNode instanceof LookupSwitchInsnNode) {
                        LookupSwitchInsnNode lsi = (LookupSwitchInsnNode) insnNode;
                        int jump = insns.indexOf(lsi.dflt);
                        merge(jump);
                        newControlFlowEdge(insn, jump);
                        for (int j = 0; j < lsi.labels.size(); ++j) {
                            LabelNode label = lsi.labels.get(j);
                            jump = insns.indexOf(label);
                            merge(jump);
                            newControlFlowEdge(insn, jump);
                        }
                    } else if (insnNode instanceof TableSwitchInsnNode) {
                        TableSwitchInsnNode tsi = (TableSwitchInsnNode) insnNode;
                        int jump = insns.indexOf(tsi.dflt);
                        merge(jump);
                        newControlFlowEdge(insn, jump);
                        for (int j = 0; j < tsi.labels.size(); ++j) {
                            LabelNode label = tsi.labels.get(j);
                            jump = insns.indexOf(label);
                            merge(jump);
                            newControlFlowEdge(insn, jump);
                        }
                    } else if (insnOpcode != ATHROW && (insnOpcode < IRETURN || insnOpcode > RETURN)) {
                        merge(insn + 1);
                        newControlFlowEdge(insn, insn + 1);
                    }
                }

                List<TryCatchBlockNode> insnHandlers = handlers[insn];
                if (insnHandlers != null) {
                    for (TryCatchBlockNode tcb : insnHandlers) {
                        newControlFlowExceptionEdge(insn, insns.indexOf(tcb.handler));
                        merge(insns.indexOf(tcb.handler));
                    }
                }
            } catch (AnalyzerException e) {
                throw new AnalyzerException(e.node, "Error at instruction " + insn + ": " + e.getMessage(), e);
            } catch (Exception e) {
                throw new AnalyzerException(insnNode, "Error at instruction " + insn + ": " + e.getMessage(), e);
            }
        }
    }

    protected void newControlFlowEdge(final int insn, final int successor) {}

    protected void newControlFlowExceptionEdge(final int insn, final int successor) {}

    // -------------------------------------------------------------------------
    private void merge(final int insn) throws AnalyzerException {
        if (!wasQueued[insn]) {
            wasQueued[insn] = true;
            if (!queued[insn]) {
                queued[insn] = true;
                queue[top++] = insn;
            }
        }
    }

}
