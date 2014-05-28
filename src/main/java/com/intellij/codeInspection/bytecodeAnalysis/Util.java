package com.intellij.codeInspection.bytecodeAnalysis;

import org.objectweb.asm.Type;

public class Util {
    public static String annotationKey(Method method, Direction dir) {
        String annPrefix = annotationKey(method);
        if (dir instanceof In) {
            return annPrefix + " " + ((In)dir).paramIndex;
        } else {
            return annPrefix;
        }
    }

    public static String annotationKey(Method method) {
        if ("<init>".equals(method.methodName)) {
            return canonical(method.internalClassName) + " " +
                    simpleName(method.internalClassName) +
                    parameters(method);
        } else {
            return canonical(method.internalClassName) + " " +
                    returnType(method) + " " +
                    method.methodName +
                    parameters(method);
        }
    }

    private static String returnType(Method method) {
        return canonical(Type.getReturnType(method.methodDesc).getClassName());
    }

    public static String canonical(String internalName) {
        return internalName.replace('/', '.').replace('$', '.');
    }

    private static String simpleName(String internalName) {
        String cn = canonical(internalName);
        int lastDotIndex = cn.lastIndexOf('.');
        if (lastDotIndex == -1) {
            return cn;
        } else {
            return cn.substring(lastDotIndex + 1);
        }
    }

    private static String parameters(Method method) {
        Type[] argTypes = Type.getArgumentTypes(method.methodDesc);
        StringBuilder sb = new StringBuilder("(");
        boolean notFirst = false;
        for (Type argType : argTypes) {
            if (notFirst) {
                sb.append(", ");
            }
            else {
                notFirst = true;
            }
            sb.append(canonical(argType.getClassName()));
        }
        sb.append(')');
        return sb.toString();
    }
}
