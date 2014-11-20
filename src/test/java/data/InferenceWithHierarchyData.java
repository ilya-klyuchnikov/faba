package data;

// the essence:
// INVOKEINTERFACE - delegate to all implementations
// INVOKEVIRTUAL - delegate to:
//     1. if current class has this method: class method + all implementations
//     2. if current class has no such method: super method + all implementations
// INVOKESPECIAL - the first implementation among current class and parents
//      (for calling private methods and super.foo() methods)
// INVOKESTATIC - like invoke special - the first implementation among current class and parents.

/**
 * A simple class to explore by examples which instructions are generated by javac
 * for instance method.
 */
public class InferenceWithHierarchyData {

    public interface Bar {
        void bar();
    }

    public class BarClass {
        public void bar() {

        }
    }

    public class BarImpl extends BarClass implements Bar {

    }

    public static class A implements Bar {
        public void foo() {

        }

        @Override
        public void bar() {

        }

        public static void staticFoo() {

        }
    }

    public static class B1 extends A {
        @Override
        public void foo() {
            super.foo();
        }
    }

    public static class B2 extends A {
        @Override
        public final void foo() {
            // INVOKESPECIAL data/InferenceWithHierarchyData$A.foo ()V
            super.foo();
        }
    }

    public static class B3 extends A {

    }

    public static class C1 extends A {

    }

    public static class D1 extends C1 {
        @Override
        public void foo() {
            // INVOKESPECIAL data/InferenceWithHierarchyData$C1.foo ()V
            super.foo();
        }
    }

    public static void test(Bar bar, A a, B1 b1, B2 b2, B3 b3, BarImpl barImpl) {
        // INVOKEINTERFACE data/InferenceWithHierarchyData$Bar.bar ()V
        bar.bar();

        // INVOKEVIRTUAL data/InferenceWithHierarchyData$A.foo ()V
        a.foo();

        // INVOKEVIRTUAL data/InferenceWithHierarchyData$A.bar ()V
        a.bar();

        // INVOKEVIRTUAL data/InferenceWithHierarchyData$B1.foo ()V
        b1.foo();

        // INVOKEVIRTUAL data/InferenceWithHierarchyData$B1.bar ()V
        b1.bar();

        // INVOKEVIRTUAL data/InferenceWithHierarchyData$B2.foo ()V
        b2.foo();

        // INVOKEVIRTUAL data/InferenceWithHierarchyData$B2.bar ()V
        b2.bar();

        // INVOKEVIRTUAL data/InferenceWithHierarchyData$B3.foo ()V
        b3.foo();

        // INVOKEVIRTUAL data/InferenceWithHierarchyData$B3.bar ()V
        b3.bar();

        // INVOKEVIRTUAL data/InferenceWithHierarchyData$BarImpl.bar ()V
        barImpl.bar();

        // INVOKESTATIC data/InferenceWithHierarchyData$A.staticFoo ()V
        A.staticFoo();

        // INVOKESTATIC data/InferenceWithHierarchyData$A.staticFoo ()V
        a.staticFoo();

        // INVOKESTATIC data/InferenceWithHierarchyData$B1.staticFoo ()V
        b1.staticFoo();

        // INVOKESTATIC data/InferenceWithHierarchyData$B1.staticFoo ()V
        B1.staticFoo();
    }
}
