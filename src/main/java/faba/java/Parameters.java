package faba.java;

import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.JumpInsnNode;
import org.objectweb.asm.tree.MethodInsnNode;
import org.objectweb.asm.tree.TypeInsnNode;
import org.objectweb.asm.tree.analysis.AnalyzerException;
import org.objectweb.asm.tree.analysis.BasicInterpreter;
import org.objectweb.asm.tree.analysis.BasicValue;
import org.objectweb.asm.tree.analysis.Frame;

import java.util.*;

import static faba.java.AbstractValues.ParamValue;
import static faba.java.AbstractValues.instanceOfCheckValue;
import static faba.java.Parameters.*;
import static org.objectweb.asm.Opcodes.*;

abstract class Parameters {
    // SoP = sum of products
    static Set<Set<Key>> join(Set<Set<Key>> sop1, Set<Set<Key>> sop2) {
        Set<Set<Key>> sop = new HashSet<Set<Key>>();
        sop.addAll(sop1);
        sop.addAll(sop2);
        return sop;
    }

    static Set<Set<Key>> meet(Set<Set<Key>> sop1, Set<Set<Key>> sop2) {
        Set<Set<Key>> sop = new HashSet<Set<Key>>();
        for (Set<Key> prod1 : sop1) {
            for (Set<Key> prod2 : sop2) {
                Set<Key> prod = new HashSet<>();
                prod.addAll(prod1);
                prod.addAll(prod2);
                sop.add(prod);
            }
        }
        return sop;
    }

    // Results
    interface PResult {}
    static final PResult Identity = new PResult() {
        @Override
        public String toString() {
            return "Identity";
        }
    };
    static final PResult Return = new PResult() {
        @Override
        public String toString() {
            return "Return";
        }
    };
    static final PResult NPE = new PResult() {
        @Override
        public String toString() {
            return "NPE";
        }
    };
    static final class ConditionalNPE implements PResult {
        final Set<Set<Key>> sop;
        public ConditionalNPE(Set<Set<Key>> sop) {
            this.sop = sop;
        }

        public ConditionalNPE(Key key) {
            sop = new HashSet<Set<Key>>();
            Set<Key> prod = new HashSet<Key>();
            prod.add(key);
            sop.add(prod);
        }
    }

    static PResult join(PResult r1, PResult r2) {
        if (Identity == r1) return r2;
        if (Identity == r2) return r1;
        if (Return == r1) return Return;
        if (Return == r2) return Return;
        if (NPE == r1) return r2;
        if (NPE == r2) return r1;
        ConditionalNPE cnpe1 = (ConditionalNPE) r1;
        ConditionalNPE cnpe2 = (ConditionalNPE) r2;
        return new ConditionalNPE(join(cnpe1.sop, cnpe2.sop));
    }

    static PResult meet(PResult r1, PResult r2) {
        if (Identity == r1) return r2;
        if (Identity == r2) return r1;
        if (Return == r1) return r2;
        if (Return == r2) return r1;
        if (NPE == r1) return NPE;
        if (NPE == r2) return NPE;
        ConditionalNPE cnpe1 = (ConditionalNPE) r1;
        ConditionalNPE cnpe2 = (ConditionalNPE) r2;
        return new ConditionalNPE(meet(cnpe1.sop, cnpe2.sop));
    }

}

class NonNullInAnalysis extends Analysis<PResult> {

    private static final NonNullInInterpreter interpreter = new NonNullInInterpreter();
    private final Key parameter;

    protected NonNullInAnalysis(RichControlFlow richControlFlow, Direction direction) {
        super(richControlFlow, direction);
        parameter = new Key(method, direction);
    }

    @Override
    PResult identity() {
        return Identity;
    }

    @Override
    PResult combineResults(PResult delta, List<PResult> subResults) {
        PResult subResult = Identity;
        for (PResult sr : subResults) {
            subResult = join(subResult, sr);
        }
        return meet(delta, subResult);
    }

    @Override
    boolean isEarlyResult(PResult result) {
        return false;
    }

    @Override
    Equation<Key, Value> mkEquation(PResult result) {
        Objects.requireNonNull(result);
        if (Identity == result || Return == result) {
            return new Equation<>(parameter, new Final<Key, Value>(Value.Top));
        }
        else if (NPE == result) {
            return new Equation<>(parameter, new Final<Key, Value>(Value.NotNull));
        }
        else {
            ConditionalNPE condNpe = (ConditionalNPE) result;
            Set<Component<Key>> components = new HashSet<>();
            for (Set<Key> prod : condNpe.sop) {
                components.add(new Component<>(false, prod));
            }
            return new Equation<>(parameter, new Pending<>(Value.NotNull, components));
        }
    }

    private int id = 0;
    private Frame<BasicValue> nextFrame = null;
    private PResult subResult = null;

    @Override
    void processState(State state) throws AnalyzerException {
        int stateIndex = state.index;
        Conf conf = state.conf;
        int insnIndex = conf.insnIndex;
        List<Conf> history = state.history;
        boolean taken = state.taken;
        Frame<BasicValue> frame = conf.frame;
        AbstractInsnNode insnNode = methodNode.instructions.get(insnIndex);
        List<Conf> nextHistory = dfsTree.loopEnters.contains(insnIndex) ? append(history, conf) : history;
        boolean hasCompanions = state.hasCompanions;
        execute(frame, insnNode);

        boolean notEmptySubResult = subResult != Identity;

        if (subResult == NPE) {
            results.put(stateIndex, NPE);
            computed.put(insnIndex, append(computed.get(insnIndex), state));
            return;
        }

        int opcode = insnNode.getOpcode();
        switch (opcode) {
            case ARETURN:
            case IRETURN:
            case LRETURN:
            case FRETURN:
            case DRETURN:
            case RETURN:
                if (!hasCompanions) {
                    earlyResult = Return;
                } else {
                    results.put(stateIndex, Return);
                    computed.put(insnIndex, append(computed.get(insnIndex), state));
                }
                return;
            default:
        }

        if (opcode == ATHROW) {
            if (taken) {
                results.put(stateIndex, NPE);
            } else {
                results.put(stateIndex, Identity);
            }
            computed.put(insnIndex, append(computed.get(insnIndex), state));
            return;
        }

        if (opcode == IFNONNULL ) {
            BasicValue popped = popValue(frame);
            if (popped instanceof ParamValue) {
                int nextInsnIndex = insnIndex + 1;
                State nextState = new State(++id, new Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult);
                pending.push(new MakeResult<PResult>(state, subResult, Collections.singletonList(nextState.index)));
                pending.push(new ProceedState<PResult>(nextState));
                return;
            }
        }

        if (opcode == IFNULL && popValue(frame) instanceof ParamValue) {
            int nextInsnIndex = methodNode.instructions.indexOf(((JumpInsnNode)insnNode).label);
            State nextState = new State(++id, new Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult);
            pending.push(new MakeResult<PResult>(state, subResult, Collections.singletonList(nextState.index)));
            pending.push(new ProceedState<PResult>(nextState));
            return;
        }

        if (opcode == IFEQ && popValue(frame) == instanceOfCheckValue) {
            int nextInsnIndex = methodNode.instructions.indexOf(((JumpInsnNode)insnNode).label);
            State nextState = new State(++id, new Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult);
            pending.push(new MakeResult<PResult>(state, subResult, Collections.singletonList(nextState.index)));
            pending.push(new ProceedState<PResult>(nextState));
            return;
        }

        if (opcode == IFNE && popValue(frame) == instanceOfCheckValue) {
            int nextInsnIndex = insnIndex + 1;
            State nextState = new State(++id, new Conf(nextInsnIndex, nextFrame), nextHistory, true, hasCompanions || notEmptySubResult);
            pending.push(new MakeResult<PResult>(state, subResult, Collections.singletonList(nextState.index)));
            pending.push(new ProceedState<PResult>(nextState));
            return;
        }

        // general case
        List<Integer> nextInsnIndices = controlFlow.transitions[insnIndex];
        List<State> nextStates = new ArrayList<>();
        List<Integer> subIndices = new ArrayList<>();
        for (int nextInsnIndex : nextInsnIndices) {
            Frame<BasicValue> nextFrame1 = nextFrame;
            if (controlFlow.errorTransitions.contains(new Edge(insnIndex, nextInsnIndex))) {
                nextFrame1 = new Frame<>(frame);
                nextFrame1.clearStack();
                nextFrame1.push(new BasicValue(Type.getType("java/lang/Throwable")));
            }
            nextStates.add(new State(++id, new Conf(nextInsnIndex, nextFrame1), nextHistory, taken, hasCompanions || notEmptySubResult));
            subIndices.add(id);
        }

        pending.push(new MakeResult<PResult>(state, subResult, subIndices));
        for (State nextState : nextStates) {
            pending.push(new ProceedState<PResult>(nextState));
        }

    }

    private <A> List<A> append(List<A> xs, A x) {
        ArrayList<A> result = new ArrayList<A>();
        if (xs != null) {
            result.addAll(xs);
        }
        result.add(x);
        return result;
    }


    private void execute(Frame<BasicValue> frame, AbstractInsnNode insnNode) throws AnalyzerException {
        switch (insnNode.getType()) {
            case AbstractInsnNode.LABEL:
            case AbstractInsnNode.LINE:
            case AbstractInsnNode.FRAME:
                nextFrame = frame;
                subResult = Identity;
                break;
            default:
                nextFrame = new Frame<>(frame);
                interpreter.reset();
                nextFrame.execute(insnNode, interpreter);
                subResult = interpreter.getSubResult();
        }
    }
}

class NonNullInInterpreter extends BasicInterpreter {
    private PResult subResult = Identity;
    public PResult getSubResult() {
        return subResult;
    }
    void reset() {
        subResult = Identity;
    }

    @Override
    public BasicValue unaryOperation(AbstractInsnNode insn, BasicValue value) throws AnalyzerException {
        switch (insn.getOpcode()) {
            case GETFIELD:
            case ARRAYLENGTH:
            case MONITORENTER:
                if (value instanceof ParamValue) {
                    subResult = NPE;
                }
                break;
            case CHECKCAST:
                if (value instanceof ParamValue) {
                    return new ParamValue(Type.getObjectType(((TypeInsnNode)insn).desc));
                }
                break;
            case INSTANCEOF:
                if (value instanceof ParamValue) {
                    return instanceOfCheckValue;
                }
                break;
            default:

        }
        return super.unaryOperation(insn, value);
    }

    @Override
    public BasicValue binaryOperation(AbstractInsnNode insn, BasicValue value1, BasicValue value2) throws AnalyzerException {
        switch (insn.getOpcode()) {
            case IALOAD:
            case LALOAD:
            case FALOAD:
            case DALOAD:
            case AALOAD:
            case BALOAD:
            case CALOAD:
            case SALOAD:
            case PUTFIELD:
                if (value1 instanceof ParamValue) {
                    subResult = NPE;
                }
                break;
            default:
        }
        return super.binaryOperation(insn, value1, value2);
    }

    @Override
    public BasicValue ternaryOperation(AbstractInsnNode insn, BasicValue value1, BasicValue value2, BasicValue value3) throws AnalyzerException {
        switch (insn.getOpcode()) {
            case IASTORE:
            case LASTORE:
            case FASTORE:
            case DASTORE:
            case AASTORE:
            case BASTORE:
            case CASTORE:
            case SASTORE:
                if (value1 instanceof ParamValue) {
                    subResult = NPE;
                }
            default:
        }
        return super.ternaryOperation(insn, value1, value2, value3);
    }

    @Override
    public BasicValue naryOperation(AbstractInsnNode insn, List<? extends BasicValue> values) throws AnalyzerException {
        int opcode = insn.getOpcode();
        boolean isStaticInvoke = opcode == INVOKESTATIC;
        int shift = isStaticInvoke ? 0 : 1;
        if (opcode != MULTIANEWARRAY && !isStaticInvoke && values.get(0) instanceof ParamValue) {
            subResult = NPE;
        }
        switch (opcode) {
            case INVOKESTATIC:
            case INVOKESPECIAL:
                MethodInsnNode methodNode = (MethodInsnNode) insn;
                for (int i = shift; i < values.size(); i++) {
                    if (values.get(i) instanceof ParamValue) {
                        Method method = new Method(methodNode.owner, methodNode.name, methodNode.desc);
                        subResult = meet(subResult, new ConditionalNPE(new Key(method, new In(i - shift))));
                    }
                }
            default:
        }
        return super.naryOperation(insn, values);
    }
}
