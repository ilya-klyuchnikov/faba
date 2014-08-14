package faba.cfg;

import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.analysis.AnalyzerException;

import java.util.List;

/**
 * Specialized lite version of {@link faba.cfg.FramelessAnalyzer}.
 * No processing of Subroutines. Should be used for methods without JSR/RET instructions.
 */
public class LiteFramelessAnalyzer extends FramelessAnalyzer {

    @Override
    protected void findSubroutine(int insn, FramelessAnalyzer.Subroutine sub, List<AbstractInsnNode> calls) throws AnalyzerException {
    }

    protected void merge(final int insn, final FramelessAnalyzer.Subroutine subroutine) throws AnalyzerException {
        if (!wasQueued[insn]) {
            wasQueued[insn] = true;
            if (!queued[insn]) {
                queued[insn] = true;
                queue[top++] = insn;
            }
        }
    }

    protected void merge(final int insn, final FramelessAnalyzer.Subroutine subroutineBeforeJSR, final boolean[] access) throws AnalyzerException {
        if (!wasQueued[insn]) {
            wasQueued[insn] = true;
            if (!queued[insn]) {
                queued[insn] = true;
                queue[top++] = insn;
            }
        }
    }
}
