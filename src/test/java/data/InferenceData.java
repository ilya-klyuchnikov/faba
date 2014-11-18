package data;

import annotations.ExpectContract;
import annotations.ExpectNotNull;
import annotations.ExpectNullable;

public class InferenceData {

    static void f(@ExpectNotNull Object o1, @ExpectNotNull Object o2) {
        if (o1 == null) throw new NullPointerException();
        else s(o2, o2);
    }

    static void g(@ExpectNotNull Object o, boolean b) {
        if (b) f(o, o);
        else s(o, o);
    }

    static void s(@ExpectNotNull Object o1, @ExpectNullable Object o2) {
        t(o1);
        v(o2);
    }

    static void t(@ExpectNotNull Object o) {
        o.toString();
    }


    static void v(@ExpectNullable Object o) {

    }

    @ExpectContract("!null->!null;null->null")
    static Object id(Object o) {
        return o;
    }

    // we do not expect not null here
    public static void notNullCompromise(Object o) {
        while (true) {
            t(o);
        }
    }

    public static void nullableCompromise(@ExpectNullable Object o1, @ExpectNullable Object o2) {
        while (true) {
            v(o1);
        }
    }

}
