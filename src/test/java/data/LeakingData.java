package data;

import annotations.ExpectLeaking;

/**
 * Test data for LeakingParameters analysis
 */
public class LeakingData {

    int z;

    void test01(@ExpectLeaking Object o1, @ExpectLeaking Object o2, @ExpectLeaking Object o3) {
        o1.toString();
        o2.toString();
        o3.toString();
    }

    void test02(@ExpectLeaking LeakingData d) {
        System.out.println(d.z);
    }

    void test03(int i, @ExpectLeaking LeakingData d) {
        System.out.println(d.z);
    }

    void test04(long i, @ExpectLeaking LeakingData d) {
        System.out.println(d.z);
    }
}
