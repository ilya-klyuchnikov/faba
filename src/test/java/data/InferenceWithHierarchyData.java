package data;

import annotations.ExpectNotNull;
import annotations.ExpectVirtualNotNull;

/**
 * @author lambdamix
 */
public interface InferenceWithHierarchyData {

    // the single class in the hierarchy, so @ExpectVirtualNotNull = @ExpectNotNull
    public class A {
        public void m1(@ExpectNotNull @ExpectVirtualNotNull Object o) {
            o.toString();
        }
    }

    public abstract class B1 {
        public void m1(@ExpectNotNull @ExpectVirtualNotNull Object o) {
            o.toString();
        }

        public void m2(@ExpectNotNull Object o) {
            o.toString();
        }

        abstract void m3(@ExpectVirtualNotNull Object o);
    }

    public class B2 extends B1 {
        @Override
        public void m2(Object o) {

        }

        @Override
        void m3(@ExpectNotNull @ExpectVirtualNotNull Object o) {
            o.toString();
        }
    }

    public interface I {
        void m(@ExpectVirtualNotNull Object o);
    }

    public class Impl implements I {

        @Override
        public void m(@ExpectNotNull @ExpectVirtualNotNull Object o) {
            o.hashCode();
        }
    }

    // interface
    //   @NotNull implementation
    //   abstract method
    //      Nullable implementation
    public interface I1 {
        public void m(Object o);
    }

    public class I1Impl implements I1 {

        @Override
        public void m(@ExpectVirtualNotNull @ExpectNotNull Object o) {
            o.toString();
        }
    }

    public abstract class I1Abs implements I1 {
        public abstract void m(Object o);
    }

    public class I1AbsImpl extends I1Abs {

        @Override
        public void m(Object o) {

        }
    }
}
