package faba.java;


import org.objectweb.asm.*;
import org.objectweb.asm.tree.MethodNode;
import org.objectweb.asm.tree.analysis.AnalyzerException;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class JavaProcessor implements Processor {
    final static ELattice<Value> valueLattice = new ELattice<Value>(Value.Bot, Value.Top);
    final Solver<Key, Value> solver = new Solver<>(valueLattice);
    final Map<Method, MethodExtra> extras = new HashMap<>();

    @Override
    public void processClass(final ClassReader classReader) {
        classReader.accept(new ClassVisitor(Opcodes.ASM5) {
            @Override
            public MethodVisitor visitMethod(int access, String name, String desc, String signature, String[] exceptions) {
                final MethodNode node = new MethodNode(Opcodes.ASM5, access, name, desc, signature, exceptions);
                return new MethodVisitor(Opcodes.ASM5, node) {
                    @Override
                    public void visitEnd() {
                        super.visitEnd();
                        processMethod(classReader.getClassName(), node);
                    }
                };
            }
        }, 0);
    }

    void processMethod(String className, MethodNode methodNode) {
        Method method = new Method(className, methodNode.name, methodNode.desc);
        extras.put(method, new MethodExtra(methodNode.signature, methodNode.access));

        ControlFlowGraph graph = cfg.buildControlFlowGraph(className, methodNode);
        boolean added = false;
        Type[] argumentTypes = Type.getArgumentTypes(methodNode.desc);
        Type resultType = Type.getReturnType(methodNode.desc);
        int resultSort = resultType.getSort();

        boolean isReferenceResult = resultSort == Type.OBJECT || resultSort == Type.ARRAY;
        boolean isBooleanResult = Type.BOOLEAN_TYPE == resultType;

        if (graph.transitions.length > 0) {
            DFSTree dfs = cfg.buildDFSTree(graph.transitions);
            boolean reducible = dfs.back.isEmpty() || cfg.reducible(graph, dfs);
            if (reducible) {
                List<Equation<Key, Value>> toAdd = new LinkedList<>();
                try {
                    for (int i = 0; i < argumentTypes.length; i++) {
                        Type argType = argumentTypes[i];
                        int argSort = argType.getSort();
                        boolean isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY;
                        boolean isBooleanArg = Type.BOOLEAN_TYPE.equals(argType);
                        if (isReferenceArg) {
                            toAdd.add(new NonNullInAnalysis(new RichControlFlow(graph, dfs), new In(i)).analyze());
                        }
                        if (isReferenceResult || isBooleanResult) {
                            if (isReferenceArg) {
                                toAdd.add(new InOutAnalysis(new RichControlFlow(graph, dfs), new InOut(i, Value.Null)).analyze());
                                toAdd.add(new InOutAnalysis(new RichControlFlow(graph, dfs), new InOut(i, Value.NotNull)).analyze());
                            }
                            if (isBooleanArg) {
                                toAdd.add(new InOutAnalysis(new RichControlFlow(graph, dfs), new InOut(i, Value.False)).analyze());
                                toAdd.add(new InOutAnalysis(new RichControlFlow(graph, dfs), new InOut(i, Value.True)).analyze());
                            }
                        }
                    }
                    if (isReferenceResult) {
                        toAdd.add(new InOutAnalysis(new RichControlFlow(graph, dfs), new Out()).analyze());
                    }
                    added = true;
                    for (Equation<Key, Value> equation : toAdd) {
                        solver.addEquation(equation);
                    }
                } catch (AnalyzerException e) {
                    throw new RuntimeException();
                }
            } else {
                System.out.println("CFG for " +
                        className + " " +
                        methodNode.name +
                        methodNode.desc + " " +
                        "is not reducible");
            }
        }

        if (!added) {
            method = new Method(className, methodNode.name, methodNode.desc);
            for (int i = 0; i < argumentTypes.length; i++) {
                Type argType = argumentTypes[i];
                int argSort = argType.getSort();
                boolean isReferenceArg = argSort == Type.OBJECT || argSort == Type.ARRAY;

                if (isReferenceArg) {
                    solver.addEquation(new Equation<Key, Value>(new Key(method, new In(i)), new Final<Key, Value>(Value.Top)));
                    if (isReferenceResult || isBooleanResult) {
                        solver.addEquation(new Equation<Key, Value>(new Key(method, new InOut(i, Value.Null)), new Final<Key, Value>(Value.Top)));
                        solver.addEquation(new Equation<Key, Value>(new Key(method, new InOut(i, Value.NotNull)), new Final<Key, Value>(Value.Top)));
                    }
                }
                if (Type.BOOLEAN_TYPE.equals(argType)) {
                    if (isReferenceResult || isBooleanResult) {
                        solver.addEquation(new Equation<Key, Value>(new Key(method, new InOut(i, Value.False)), new Final<Key, Value>(Value.Top)));
                        solver.addEquation(new Equation<Key, Value>(new Key(method, new InOut(i, Value.True)), new Final<Key, Value>(Value.Top)));
                    }
                }
            }
            if (isReferenceResult) {
                solver.addEquation(new Equation<Key, Value>(new Key(method, new Out()), new Final<Key, Value>(Value.Top)));
            }
        }

    }
}
