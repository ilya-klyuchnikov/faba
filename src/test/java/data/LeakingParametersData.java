package data;

import annotations.ExpectLeaking;

import java.util.Collections;


public class LeakingParametersData {

    int z;

    // dereferenced parameter is a leaking one
    void dereferencedParameter1(long i, @ExpectLeaking LeakingParametersData d) {
        System.out.println(d.z);
    }

    // dereferenced parameter is a leaking one
    void dereferencedParameter2(@ExpectLeaking Object o1, @ExpectLeaking Object o2, @ExpectLeaking Object o3) {
        o1.toString();
        o2.toString();
        o3.toString();
    }

    // parameter passed to another method is a leaking one
    void passedToMethodParameter(@ExpectLeaking Object o1) {
        Collections.singleton(o1);
    }

    //
    Object parameterBranching(@ExpectLeaking Object o1) {
        if (o1 == null) {
            return null;
        }
        return this;
    }

    // returned parameter is a leaking one
    Object returnedParameter(@ExpectLeaking Object o) {
        return o;
    }

    Object returnedParameterInCycle(@ExpectLeaking Object o) {
        while (z < 10) {
            z++;
        }
        o.hashCode();
        return o;
    }
}
