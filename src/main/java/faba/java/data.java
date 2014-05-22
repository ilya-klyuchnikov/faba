package faba.java;

final class MethodExtra {
    final String signature;
    final int access;

    MethodExtra(String signature, int access) {
        this.signature = signature;
        this.access = access;
    }
}

final class Method {
    final String internalClassName;
    final String methodName;
    final String methodDesc;

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Method method = (Method) o;
        return internalClassName.equals(method.internalClassName) && methodDesc.equals(method.methodDesc) && methodName.equals(method.methodName);
    }

    @Override
    public int hashCode() {
        int result = internalClassName.hashCode();
        result = 31 * result + methodName.hashCode();
        result = 31 * result + methodDesc.hashCode();
        return result;
    }

    Method(String internalClassName, String methodName, String methodDesc) {
        this.internalClassName = internalClassName;
        this.methodName = methodName;
        this.methodDesc = methodDesc;
    }

    @Override
    public String toString() {
        return "Method(" +
                internalClassName + ',' +
                methodName + ',' +
                methodDesc +
                ')';
    }
}

enum Value {
    Bot, NotNull, Null, True, False, Top
}

// for tests
enum Nullity {
    NotNull, Nullable
}

interface Direction {}
final class In implements Direction {
    final int paramIndex;

    In(int paramIndex) {
        this.paramIndex = paramIndex;
    }
}

final class InOut implements Direction {
    final int paramIndex;
    final Value value;

    InOut(int paramIndex, Value value) {
        this.paramIndex = paramIndex;
        this.value = value;
    }
}

final class Out implements Direction {}

final class Key {
    final Method method;
    final Direction direction;

    Key(Method method, Direction direction) {
        this.method = method;
        this.direction = direction;
    }
}


