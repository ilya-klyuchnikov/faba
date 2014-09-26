package faba.asm;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.tree.*;
import org.objectweb.asm.tree.analysis.AnalyzerException;

public class FastBasicInterpreter extends FastInterpreter implements Opcodes {

    public FastBasicInterpreter() {
        super();
    }

    @Override
    public int newValue(final Type type) {
        if (type == null) {
            return FastValues.ANY_VAL;
        }
        switch (type.getSort()) {
            case Type.LONG:
            case Type.DOUBLE:
                return FastValues.DOUBLE_OR_LONG;
            default:
                return FastValues.ANY_VAL;
        }
    }

    @Override
    public int newOperation(final AbstractInsnNode insn) throws AnalyzerException {
        switch (insn.getOpcode()) {
            case LCONST_0:
            case LCONST_1:
            case DCONST_0:
            case DCONST_1:
                return FastValues.DOUBLE_OR_LONG;
            case LDC:
                Object cst = ((LdcInsnNode) insn).cst;
                if (cst instanceof Long || cst instanceof Double) {
                    return FastValues.DOUBLE_OR_LONG;
                } else {
                    return FastValues.ANY_VAL;
                }
            case GETSTATIC:
                return newValue(Type.getType(((FieldInsnNode) insn).desc));
            default:
                return FastValues.ANY_VAL;
        }
    }

    @Override
    public int copyOperation(final AbstractInsnNode insn, final int value) throws AnalyzerException {
        return value;
    }

    @Override
    public int unaryOperation(final AbstractInsnNode insn, final int value) throws AnalyzerException {
        switch (insn.getOpcode()) {
            case LNEG:
            case I2L:
            case F2L:
            case D2L:
            case DNEG:
            case I2D:
            case L2D:
            case F2D:
                return FastValues.DOUBLE_OR_LONG;
            case GETFIELD:
                return newValue(Type.getType(((FieldInsnNode) insn).desc));
            default:
                return FastValues.ANY_VAL;
        }
    }

    @Override
    public int binaryOperation(AbstractInsnNode insn, int value1, int value2) throws AnalyzerException {
        switch (insn.getOpcode()) {
            case LALOAD:
            case LADD:
            case LSUB:
            case LMUL:
            case LDIV:
            case LREM:
            case LSHL:
            case LSHR:
            case LUSHR:
            case LAND:
            case LOR:
            case LXOR:
            case DALOAD:
            case DADD:
            case DSUB:
            case DMUL:
            case DDIV:
            case DREM:
                return FastValues.DOUBLE_OR_LONG;
            default:
                return FastValues.ANY_VAL;
        }
    }

    @Override
    public int ternaryOperation(final AbstractInsnNode insn, final int value1, final int value2, final int value3) throws AnalyzerException {
        return FastValues.ANY_VAL;
    }

    @Override
    public int naryOperation(final AbstractInsnNode insn, final int[] values) throws AnalyzerException {
        int opcode = insn.getOpcode();
        if (opcode == MULTIANEWARRAY) {
            return FastValues.ANY_VAL;
        } else if (opcode == INVOKEDYNAMIC) {
            return newValue(Type.getReturnType(((InvokeDynamicInsnNode) insn).desc));
        } else {
            return newValue(Type.getReturnType(((MethodInsnNode) insn).desc));
        }
    }

    @Override
    public void returnOperation(final AbstractInsnNode insn, final int value) {}

    @Override
    public int merge(int v, int w) {
        if (v != w) {
            return FastValues.ANY_VAL;
        }
        return v;
    }
}
