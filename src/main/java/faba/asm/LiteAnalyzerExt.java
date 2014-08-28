/***
 * ASM: a very small and fast Java bytecode manipulation framework
 * Copyright (c) 2000-2011 INRIA, France Telecom
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holders nor the names of its
 *    contributors may be used to endorse or promote products derived from
 *    this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
 * THE POSSIBILITY OF SUCH DAMAGE.
 */
package faba.asm;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.*;
import org.objectweb.asm.tree.analysis.AnalyzerException;
import org.objectweb.asm.tree.analysis.Frame;
import org.objectweb.asm.tree.analysis.Interpreter;
import org.objectweb.asm.tree.analysis.Value;

import java.util.ArrayList;
import java.util.List;

/**
 * Extended version of {@link org.objectweb.asm.tree.analysis.Analyzer}.
 * It handles frames <b>and</b> additional user info.
 */
public class LiteAnalyzerExt<V extends Value, Data, MyInterpreter extends Interpreter<V> & InterpreterExt<Data>> implements Opcodes {

    private final MyInterpreter interpreter;

    private Frame<V>[] frames;

    private boolean[] queued;

    private int[] queue;

    private int top;

    public Data[] getData() {
        return data;
    }

    private Data[] data;

    public LiteAnalyzerExt(final MyInterpreter interpreter, Data[] data, Data startData) {
        this.interpreter = interpreter;
        this.data = data;
        if (data.length > 0) {
            data[0] = startData;
        }
    }

    public Frame<V>[] analyze(final String owner, final MethodNode m)
            throws AnalyzerException {
        if ((m.access & (ACC_ABSTRACT | ACC_NATIVE)) != 0) {
            frames = (Frame<V>[]) new Frame<?>[0];
            return frames;
        }
        int n = m.instructions.size();
        InsnList insns = m.instructions;
        List<TryCatchBlockNode>[] handlers = (List<TryCatchBlockNode>[]) new List<?>[n];
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

        interpreter.init(data[0]);
        merge(0, current);

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

                if (insnType == AbstractInsnNode.LABEL || insnType == AbstractInsnNode.LINE || insnType == AbstractInsnNode.FRAME) {
                    interpreter.init(data[insn]);
                    merge(insn + 1, f);
                } else {
                    // delta
                    interpreter.init(data[insn]);
                    current.init(f).execute(insnNode, interpreter);

                    if (insnNode instanceof JumpInsnNode) {
                        JumpInsnNode j = (JumpInsnNode) insnNode;
                        if (insnOpcode != GOTO && insnOpcode != JSR) {
                            merge(insn + 1, current);
                        }
                        int jump = insns.indexOf(j.label);
                        merge(jump, current);
                    } else if (insnNode instanceof LookupSwitchInsnNode) {
                        LookupSwitchInsnNode lsi = (LookupSwitchInsnNode) insnNode;
                        int jump = insns.indexOf(lsi.dflt);
                        merge(jump, current);
                        for (int j = 0; j < lsi.labels.size(); ++j) {
                            LabelNode label = lsi.labels.get(j);
                            jump = insns.indexOf(label);
                            merge(jump, current);
                        }
                    } else if (insnNode instanceof TableSwitchInsnNode) {
                        TableSwitchInsnNode tsi = (TableSwitchInsnNode) insnNode;
                        int jump = insns.indexOf(tsi.dflt);
                        merge(jump, current);
                        for (int j = 0; j < tsi.labels.size(); ++j) {
                            LabelNode label = tsi.labels.get(j);
                            jump = insns.indexOf(label);
                            merge(jump, current);
                        }
                    } else if (insnOpcode != ATHROW
                            && (insnOpcode < IRETURN || insnOpcode > RETURN)) {
                        merge(insn + 1, current);
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
                        handler.init(f);
                        handler.clearStack();
                        handler.push(interpreter.newValue(type));
                        merge(jump, handler);
                    }
                }
            } catch (AnalyzerException e) {
                throw new AnalyzerException(e.node, "Error at instruction "
                        + insn + ": " + e.getMessage(), e);
            } catch (Exception e) {
                throw new AnalyzerException(insnNode, "Error at instruction "
                        + insn + ": " + e.getMessage(), e);
            }
        }

        return frames;
    }

    public Frame<V>[] getFrames() {
        return frames;
    }

    protected Frame<V> newFrame(final int nLocals, final int nStack) {
        return new Frame<V>(nLocals, nStack);
    }

    protected Frame<V> newFrame(final Frame<? extends V> src) {
        return new Frame<V>(src);
    }

    // -------------------------------------------------------------------------

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

        // delta
        mergeData(insn, interpreter);
    }

    private void mergeData(int insn, MyInterpreter interpreter) {
        boolean changes = false;

        Data oldData = data[insn];
        Data newData = interpreter.getAfterData(insn);

        if (oldData == null) {
            data[insn] = newData;
            changes = true;
        } else if (newData != null) {
            Data mergedData = interpreter.merge(oldData, newData);
            data[insn] = mergedData;
            changes = !oldData.equals(mergedData);
        }

        if (changes && !queued[insn]) {
            queued[insn] = true;
            queue[top++] = insn;
        }
    }
}
