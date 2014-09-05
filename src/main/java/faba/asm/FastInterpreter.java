package faba.asm;

import org.objectweb.asm.Type;
import org.objectweb.asm.tree.AbstractInsnNode;
import org.objectweb.asm.tree.analysis.AnalyzerException;

/**
 * Specialization of {@link org.objectweb.asm.tree.analysis.Interpreter} to work with
 * symbolic values encoded as integers.
 *
 */
public abstract class FastInterpreter {

    protected FastInterpreter() {
    }

    /**
     * Creates a new value that represents the given type.
     *
     * Called for method parameters (including <code>this</code>), exception
     * handler variable and with <code>null</code> type for variables reserved
     * by long and double types.
     *
     * @param type
     *            a primitive or reference type, or <tt>null</tt> to represent
     *            an uninitialized value.
     * @return a value that represents the given type. The size of the returned
     *         value must be equal to the size of the given type.
     */
    public abstract int newValue(Type type);

    /**
     * Interprets a bytecode instruction without arguments. This method is
     * called for the following opcodes:
     *
     * ACONST_NULL, ICONST_M1, ICONST_0, ICONST_1, ICONST_2, ICONST_3, ICONST_4,
     * ICONST_5, LCONST_0, LCONST_1, FCONST_0, FCONST_1, FCONST_2, DCONST_0,
     * DCONST_1, BIPUSH, SIPUSH, LDC, JSR, GETSTATIC, NEW
     *
     * @param insn
     *            the bytecode instruction to be interpreted.
     * @return the result of the interpretation of the given instruction.
     * @throws org.objectweb.asm.tree.analysis.AnalyzerException
     *             if an error occured during the interpretation.
     */
    public abstract int newOperation(AbstractInsnNode insn) throws AnalyzerException;

    /**
     * Interprets a bytecode instruction that moves a value on the stack or to
     * or from local variables. This method is called for the following opcodes:
     *
     * ILOAD, LLOAD, FLOAD, DLOAD, ALOAD, ISTORE, LSTORE, FSTORE, DSTORE,
     * ASTORE, DUP, DUP_X1, DUP_X2, DUP2, DUP2_X1, DUP2_X2, SWAP
     *
     * @param insn
     *            the bytecode instruction to be interpreted.
     * @param value
     *            the value that must be moved by the instruction.
     * @return the result of the interpretation of the given instruction. The
     *         returned value must be <tt>equal</tt> to the given value.
     * @throws AnalyzerException
     *             if an error occured during the interpretation.
     */
    public abstract int copyOperation(AbstractInsnNode insn, int value) throws AnalyzerException;

    /**
     * Interprets a bytecode instruction with a single argument. This method is
     * called for the following opcodes:
     *
     * INEG, LNEG, FNEG, DNEG, IINC, I2L, I2F, I2D, L2I, L2F, L2D, F2I, F2L,
     * F2D, D2I, D2L, D2F, I2B, I2C, I2S, IFEQ, IFNE, IFLT, IFGE, IFGT, IFLE,
     * TABLESWITCH, LOOKUPSWITCH, IRETURN, LRETURN, FRETURN, DRETURN, ARETURN,
     * PUTSTATIC, GETFIELD, NEWARRAY, ANEWARRAY, ARRAYLENGTH, ATHROW, CHECKCAST,
     * INSTANCEOF, MONITORENTER, MONITOREXIT, IFNULL, IFNONNULL
     *
     * @param insn
     *            the bytecode instruction to be interpreted.
     * @param value
     *            the argument of the instruction to be interpreted.
     * @return the result of the interpretation of the given instruction.
     * @throws AnalyzerException
     *             if an error occured during the interpretation.
     */
    public abstract int unaryOperation(AbstractInsnNode insn, int value) throws AnalyzerException;

    /**
     * Interprets a bytecode instruction with two arguments. This method is
     * called for the following opcodes:
     *
     * IALOAD, LALOAD, FALOAD, DALOAD, AALOAD, BALOAD, CALOAD, SALOAD, IADD,
     * LADD, FADD, DADD, ISUB, LSUB, FSUB, DSUB, IMUL, LMUL, FMUL, DMUL, IDIV,
     * LDIV, FDIV, DDIV, IREM, LREM, FREM, DREM, ISHL, LSHL, ISHR, LSHR, IUSHR,
     * LUSHR, IAND, LAND, IOR, LOR, IXOR, LXOR, LCMP, FCMPL, FCMPG, DCMPL,
     * DCMPG, IF_ICMPEQ, IF_ICMPNE, IF_ICMPLT, IF_ICMPGE, IF_ICMPGT, IF_ICMPLE,
     * IF_ACMPEQ, IF_ACMPNE, PUTFIELD
     *
     * @param insn
     *            the bytecode instruction to be interpreted.
     * @param value1
     *            the first argument of the instruction to be interpreted.
     * @param value2
     *            the second argument of the instruction to be interpreted.
     * @return the result of the interpretation of the given instruction.
     * @throws AnalyzerException
     *             if an error occured during the interpretation.
     */
    public abstract int binaryOperation(AbstractInsnNode insn, int value1, int value2) throws AnalyzerException;

    /**
     * Interprets a bytecode instruction with three arguments. This method is
     * called for the following opcodes:
     *
     * IASTORE, LASTORE, FASTORE, DASTORE, AASTORE, BASTORE, CASTORE, SASTORE
     *
     * @param insn
     *            the bytecode instruction to be interpreted.
     * @param value1
     *            the first argument of the instruction to be interpreted.
     * @param value2
     *            the second argument of the instruction to be interpreted.
     * @param value3
     *            the third argument of the instruction to be interpreted.
     * @return the result of the interpretation of the given instruction.
     * @throws AnalyzerException
     *             if an error occured during the interpretation.
     */
    public abstract int ternaryOperation(AbstractInsnNode insn, int value1, int value2, int value3) throws AnalyzerException;

    /**
     * Interprets a bytecode instruction with a variable number of arguments.
     * This method is called for the following opcodes:
     *
     * INVOKEVIRTUAL, INVOKESPECIAL, INVOKESTATIC, INVOKEINTERFACE,
     * MULTIANEWARRAY and INVOKEDYNAMIC
     *
     * @param insn
     *            the bytecode instruction to be interpreted.
     * @param values
     *            the arguments of the instruction to be interpreted.
     * @return the result of the interpretation of the given instruction.
     * @throws AnalyzerException
     *             if an error occured during the interpretation.
     */
    public abstract int naryOperation(AbstractInsnNode insn, int[] values) throws AnalyzerException;

    /**
     * Interprets a bytecode return instruction. This method is called for the
     * following opcodes:
     *
     * IRETURN, LRETURN, FRETURN, DRETURN, ARETURN
     *
     * @param insn
     *            the bytecode instruction to be interpreted.
     * @param value
     *            the argument of the instruction to be interpreted.
     * @throws AnalyzerException
     *             if an error occured during the interpretation.
     */
    public abstract void returnOperation(AbstractInsnNode insn, int value) throws AnalyzerException;

    /**
     * Merges two values. The merge operation must return a value that
     * represents both values (for instance, if the two values are two types,
     * the merged value must be a common super type of the two types. If the two
     * values are integer intervals, the merged value must be an interval that
     * contains the previous ones. Likewise for other types of values).
     *
     * @param value1
     *            a value.
     * @param value2
     *            another value.
     * @return the merged value. If the merged value is equal to @{link value1},
     *         this method <i>must</i> return @{link value1}.
     */
    public abstract int merge(int value1, int value2);
}
