package data;

import annotations.ExpectContract;
import annotations.ExpectNotNull;

public class Data01 {

    static void f(@ExpectNotNull Object o1, @ExpectNotNull Object o2) {
        if (o1 == null) throw new NullPointerException();
        else s(o2, o2);
    }

    static void g(@ExpectNotNull Object o, boolean b) {
        if (b) f(o, o);
        else s(o, o);
    }

    static void s(@ExpectNotNull Object o1, Object o2) {
        t(o1);
        v(o2);
    }

    static void t(@ExpectNotNull Object o) {
        o.toString();
    }


    static void v(Object o) {

    }

    @ExpectContract("!null->!null;null->null")
    static Object id(Object o) {
        return o;
    }

    @ExpectContract("false->false;true->true")
    static boolean id(boolean b) {
        return b;
    }
}
