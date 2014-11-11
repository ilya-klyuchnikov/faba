package data;

import annotations.ExpectResultOrigin;

public class ResultOriginsData {

    public Object simpleReturn(@ExpectResultOrigin Object o) {
        return o;
    }

    public Object return1(@ExpectResultOrigin Object o) {
        while (true) {
            Object o1 = o.getClass();
            if (o1 == null) {
                return o;
            }
            o = o1;
        }
    }
}
