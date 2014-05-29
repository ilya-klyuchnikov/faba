package com.intellij.codeInspection.bytecodeAnalysis;

import org.objectweb.asm.Type;

import java.util.regex.Pattern;

public class Util {
    private static final Pattern REGEX_PATTERN = Pattern.compile("(?<=[^\\$\\.])\\${1}(?=[^\\$])"); // disallow .$ or $$

    public static String annotationKey(Method method, Direction dir) {
        String annPrefix = annotationKey(method);
        return (dir instanceof In)
                ? annPrefix + " " + ((In)dir).paramIndex
                : annPrefix;
    }

    public static String annotationKey(Method method) {
        return "<init>".equals(method.methodName)
                ? internalName2Idea(method.internalClassName) + ' ' + simpleName(method.internalClassName) + parameters(method)
                : internalName2Idea(method.internalClassName) + ' ' + returnType(method) + ' ' + method.methodName + parameters(method);
    }

    private static String returnType(Method method) {
        return binaryName2Idea(Type.getReturnType(method.methodDesc).getClassName());
    }

    private static String simpleName(String internalName) {
        String ideaName = internalName2Idea(internalName);
        int lastDotIndex = ideaName.lastIndexOf('.');
        return (lastDotIndex == -1)
                ? ideaName
                : ideaName.substring(lastDotIndex + 1);
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
            sb.append(binaryName2Idea(argType.getClassName()));
        }
        sb.append(')');
        return sb.toString();
    }

    public static String internalName2Idea(String internalName) {
        String binaryName = Type.getObjectType(internalName).getClassName();
        return binaryName.indexOf('$') >= 0
                ? REGEX_PATTERN.matcher(binaryName).replaceAll("\\.")
                : binaryName;
    }

    public static String binaryName2Idea(String binaryName) {
        return binaryName.indexOf('$') >= 0
                ? REGEX_PATTERN.matcher(binaryName).replaceAll("\\.")
                : binaryName;
    }
}
