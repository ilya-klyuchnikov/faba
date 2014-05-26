package com.intellij.codeInspection.bytecodeAnalysis;

import org.objectweb.asm.Opcodes;
import org.objectweb.asm.Type;
import org.objectweb.asm.signature.SignatureReader;
import org.objectweb.asm.signature.SignatureVisitor;

public class Util {
    public static String annotationKey(Method method, MethodExtra extra, Direction dir) {
        String annPrefix = annotationKey(method, extra);
        if (dir instanceof In) {
            return annPrefix + " " + ((In)dir).paramIndex;
        } else {
            return annPrefix;
        }
    }

    public static String annotationKey(Method method, MethodExtra extra) {
        if ("<init>".equals(method.methodName)) {
            return canonical(method.internalClassName) + " " +
                    simpleName(method.internalClassName) +
                    parameters(method, extra);
        } else {
            return canonical(method.internalClassName) + " " +
                    returnType(method, extra) + " " +
                    method.methodName +
                    parameters(method, extra);
        }
    }

    private static String returnType(Method method, MethodExtra extra) {
        if (extra.signature != null) {
            final StringBuilder sb = new StringBuilder();
            new SignatureReader(extra.signature).accept(new SignatureVisitor(Opcodes.ASM5) {
                @Override
                public SignatureVisitor visitReturnType() {
                    return new GenericTypeRenderer(sb);
                }
            });
            return sb.toString();
        }
        else {
            return canonical(Type.getReturnType(method.methodDesc).getClassName());
        }
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

    private static String parameters(Method method, MethodExtra extra) {
        String result;
        if (extra.signature != null) {
            GenericMethodParametersRenderer renderer = new GenericMethodParametersRenderer();
            new SignatureReader(extra.signature).accept(renderer);
            result = renderer.parameters();
        }
        else {
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
            result = sb.toString();
        }
        if ((extra.access & Opcodes.ACC_VARARGS) != 0) {
            return result.replace("[])", "...)");
        } else {
            return result;
        }
    }

    static class GenericMethodParametersRenderer extends SignatureVisitor {

        private StringBuilder sb = new StringBuilder("(");
        private boolean first = true;
        public GenericMethodParametersRenderer() {
            super(Opcodes.ASM5);
        }
        public String parameters() {
            return sb.append(')').toString();
        }

        @Override
        public SignatureVisitor visitParameterType() {
            if (first) {
                first = false;
            }
            else {
                sb.append(", ");
            }
            return new GenericTypeRenderer(sb);
        }
    }

    static class GenericTypeRenderer extends SignatureVisitor {

        final StringBuilder sb;
        private boolean angleBracketOpen = false;

        public GenericTypeRenderer(StringBuilder sb) {
            super(Opcodes.ASM5);
            this.sb = sb;
        }

        private boolean openAngleBracket() {
            if (angleBracketOpen) {
                return false;
            } else {
                angleBracketOpen = true;
                sb.append('<');
                return true;
            }
        }

        private void closeAngleBracket() {
            if (angleBracketOpen) {
                angleBracketOpen = false;
                sb.append('>');
            }
        }

        private void beforeTypeArgument() {
            boolean first = openAngleBracket();
            if (!first) {
                sb.append(',');
            }
        }

        protected void endType() {}

        @Override
        public void visitBaseType(char descriptor) {
            switch (descriptor) {
                case 'V':
                    sb.append("void");
                    break;
                case 'B':
                    sb.append("byte");
                    break;
                case 'J':
                    sb.append("long");
                    break;
                case 'Z':
                    sb.append("boolean");
                    break;
                case 'I':
                    sb.append("int");
                    break;
                case 'S':
                    sb.append("short");
                    break;
                case 'C':
                    sb.append("char");
                    break;
                case 'F':
                    sb.append("float");
                    break;
                case 'D':
                    sb.append("double");
                    break;
            }
            endType();
        }

        @Override
        public void visitTypeVariable(String name) {
            sb.append(name);
            endType();
        }

        @Override
        public SignatureVisitor visitArrayType() {
            return new GenericTypeRenderer(sb) {
                @Override
                protected void endType() {
                    sb.append("[]");
                }
            };
        }

        @Override
        public void visitClassType(String name) {
            sb.append(canonical(name));
        }

        @Override
        public void visitInnerClassType(String name) {
            closeAngleBracket();
            sb.append('.').append(canonical(name));
        }

        @Override
        public void visitTypeArgument() {
            beforeTypeArgument();
            sb.append('?');
        }

        @Override
        public SignatureVisitor visitTypeArgument(char wildcard) {
            beforeTypeArgument();
            switch (wildcard) {
                case SignatureVisitor.EXTENDS:
                    sb.append("? extends ");
                    break;
                case SignatureVisitor.SUPER:
                    sb.append("? super ");
                    break;
                case SignatureVisitor.INSTANCEOF:
                    break;
            }
            return new GenericTypeRenderer(sb);
        }

        @Override
        public void visitEnd() {
            closeAngleBracket();
            endType();
        }

    }
}
