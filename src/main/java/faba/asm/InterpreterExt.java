package faba.asm;

// calculate additional state
public interface InterpreterExt<Data> { // extends Interpreter<V>

    // during Interpreter's execution it calculates delta
    void init(Data previous);

    Data getAfterData(int insn);

    // merge two states
    Data merge(Data data1, Data data2);
}
