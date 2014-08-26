package faba.asm;

import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.LabelNode;
import org.objectweb.asm.tree.analysis.AnalyzerException;

import java.util.ArrayList;
import java.util.List;

public class Subroutine {

    LabelNode start;
    boolean[] access;
    List<JumpInsnNode> callers;

    private Subroutine() {
    }

    Subroutine(final LabelNode start, final int maxLocals,
               final JumpInsnNode caller) {
        this.start = start;
        this.access = new boolean[maxLocals];
        this.callers = new ArrayList<JumpInsnNode>();
        callers.add(caller);
    }

    public Subroutine copy() {
        Subroutine result = new Subroutine();
        result.start = start;
        result.access = new boolean[access.length];
        System.arraycopy(access, 0, result.access, 0, access.length);
        result.callers = new ArrayList<JumpInsnNode>(callers);
        return result;
    }

    public boolean merge(final Subroutine subroutine) throws AnalyzerException {
        boolean changes = false;
        for (int i = 0; i < access.length; ++i) {
            if (subroutine.access[i] && !access[i]) {
                access[i] = true;
                changes = true;
            }
        }
        if (subroutine.start == start) {
            for (int i = 0; i < subroutine.callers.size(); ++i) {
                JumpInsnNode caller = subroutine.callers.get(i);
                if (!callers.contains(caller)) {
                    callers.add(caller);
                    changes = true;
                }
            }
        }
        return changes;
    }
}
