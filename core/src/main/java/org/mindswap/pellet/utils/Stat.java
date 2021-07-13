package org.mindswap.pellet.utils;

public class Stat {
    public boolean result;
    public boolean error;
    public long time;
    public long memory;
    public long treeSize_1, treeSize_2;
    public long branches;
    public long globalRestores, localRestores, backtracks, backjumps;

    @Override
    public String toString() {
        return "Stat{" +
                "result=" + result +
                ", error=" + error +
                ", time=" + time +
                ", memory=" + memory/1000 +
                "kb, treeSize_1=" + treeSize_1 +
                ", treeSize_2=" + treeSize_2 +
                ", branches=" + branches +
                ", globalRestores=" + globalRestores +
                ", localRestores=" + localRestores +
                ", backtracks=" + backtracks +
                ", backjumps=" + backjumps +
                '}';
    }
}
