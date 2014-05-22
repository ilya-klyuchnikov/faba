package faba.java;


import org.objectweb.asm.ClassReader;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Opcodes;
import org.objectweb.asm.tree.MethodNode;

import java.io.File;
import java.util.HashMap;
import java.util.Map;

public class Main implements Processor {
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

        if (graph.transitions.length > 0) {
            DFSTree dfs = cfg.buildDFSTree(graph.transitions);
            boolean reducible = dfs.back.isEmpty() || cfg.reducible(graph, dfs);
            if (reducible) {

            } else {
                System.out.println("CFG for " +
                        className + " " +
                        methodNode.name +
                        methodNode.desc + " " +
                        "is not reducible");
            }
        }
    }

    private void process(Source source, String outDir) {
        long indexStart = System.currentTimeMillis();
        source.process(this);
        long indexEnd = System.currentTimeMillis();
    }

    public static void main(String[] args) {
        if (args.length != 2) {
            System.out.println("Usage: faba.java.Main inputJar outDir");
        } else {
            new Main().process(new JarFileSource(new File(args[0])), args[1]);
        }
    }
}
