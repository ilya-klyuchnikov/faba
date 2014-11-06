package faba.analysis;

// calculate additional state

/**
 * Trait for an interpreter (to be mixed with {@link org.objectweb.asm.tree.analysis.Interpreter})
 * which calculates additional constraints.
 * Used in NullableResultAnalysis to propagate information about not null values.
 *
 * @param <Data> the type of constraint
 */
public interface InterpreterExt<Data> { // extends Interpreter<V>

    // during Interpreter's execution it calculates delta
    void init(Data previous);

    Data getAfterData(int insn);

    // merge two states
    Data merge(Data data1, Data data2);
}
