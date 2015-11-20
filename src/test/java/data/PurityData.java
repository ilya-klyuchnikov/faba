package data;

import annotations.ExpectLocalEffect;
import annotations.ExpectPure;
import annotations.ExpectParamChange;

public class PurityData {
    private int i;

    @ExpectPure
    PurityData() {

    }

    @ExpectLocalEffect
    PurityData(int i) {
        this.i = i;
        inc();
    }

    @ExpectPure
    public static void init() {

    }

    @ExpectLocalEffect
    public final void setI(int i) {
        this.i = i;
        inc();
    }

    @ExpectLocalEffect
    private void inc() {
        i++;
    }

    public final void changeParam(@ExpectParamChange PurityData pd) {
        pd.setI(1);
    }

    public final void arraycopy(Object src,  int  srcPos,
                                @ExpectParamChange Object dest, int destPos,
                                int length) {
        System.arraycopy(src, srcPos, dest, destPos, length);
    }

    @ExpectPure
    public static boolean[] copyOf(boolean[] original, int newLength) {
        boolean[] copy = new boolean[newLength];
        System.arraycopy(original, 0, copy, 0, original.length);
        return copy;
    }

    @ExpectPure
    static Bean createBean() {
        return new Bean();
    }

    @ExpectPure
    static Bean createBean(int version) {
        return new Bean(version);
    }

    public static class Bean {
        private int version;

        @ExpectPure
        public Bean() {

        }


        @ExpectLocalEffect
        public Bean(int version) {
            this.version = version;
        }


        @ExpectPure
        public final int getVersion() {
            return version;
        }

        @ExpectLocalEffect
        public final void setVersion(int version) {
            this.version = version;
        }
    }
}
