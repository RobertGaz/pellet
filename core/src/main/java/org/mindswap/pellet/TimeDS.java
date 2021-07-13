package org.mindswap.pellet;

import aterm.ATermAppl;

import java.util.*;
import java.util.stream.Collectors;

import static java.util.stream.Collectors.groupingBy;
import static java.util.stream.Collectors.mapping;

public class TimeDS {
//    ROBERT подумать о TreeMap
    private Map<Time, DependencySet> map = new TreeMap<>();
    private Set<ATermAppl> explain = new HashSet<>();

    public TimeDS() {}
    public TimeDS(Time time, DependencySet ds) { map.put(time, ds); }
    public TimeDS(DependencySet ds) { explain = ds.getExplain(); }
    public TimeDS(Map<Time, DependencySet> map) { this.map = map; }
    public TimeDS(Set<ATermAppl> explain) { map.put(Time.universal(), new DependencySet(explain)); }
    public TimeDS(TimeDS other) {
        other.map.forEach((t, ds) -> map.put(new Time(t), ds));
        explain.addAll(other.explain);
    }
    public TimeDS copy() { return new TimeDS(this); }

    public static TimeDS universal(DependencySet ds) { return new TimeDS(Time.universal(), ds); }
    public static TimeDS INDEPENDENT() { return universal(DependencySet.INDEPENDENT); }
    public static TimeDS EMPTY() { return universal(DependencySet.EMPTY); }
    public static TimeDS DUMMY() { return universal(DependencySet.DUMMY); }
    public static TimeDS empty() { return new TimeDS(); }

    public TimeDS add(TimeDS other) {
        if (this == other) {
            return TimeDS.empty();
        }
        return add(other, false);
    }

    private TimeDS add(TimeDS other, boolean branchCheck) {
        for (Map.Entry<Time, DependencySet> entry : other.map.entrySet()) {
            add(entry.getKey(), entry.getValue(), branchCheck);
        }
        other.map.entrySet().removeIf(entry -> entry.getKey().isEmpty());
        return other;
    }

    private Time add(Time time, DependencySet ds, boolean branchCheck) {
        if (time.isEmpty()) {
            return time;
        }
        if (branchCheck) {
            map.entrySet().stream().filter(e -> e.getValue().getBranch() > ds.getBranch()).forEach(e -> e.getKey().subtract(time));
            map.entrySet().removeIf(entry -> entry.getKey().isEmpty());
        }
        time.subtract(time());
        if (!time.isEmpty()) {
            map.put(time.copy(), ds);
        }
        return time;
    }

    public int size() {
        return map.size();
    }

    public Map.Entry<Time, DependencySet> getFirstEntry() {
        return ((TreeMap<Time, DependencySet>) map).firstEntry();
    }


    public Time time() {
        Time result = new Time();
        map.keySet().forEach(result::unite);
        return result;
    }

    public DependencySet ds() {
        DependencySet result = DependencySet.EMPTY;
        for (DependencySet ds : map.values()) {
            result = ds.union(result, false);
        }
        return result;
    }

    public TimeDS partBy(Time time) {
        if (time.isEmpty() || isEmpty()) {
            return TimeDS.empty();
        }
        if (time.isUniversal()) {
            return copy();
        }

        TreeMap<Time, DependencySet> partMap = new TreeMap<>();
        map.entrySet().stream()
                .filter(entry -> entry.getKey().intersects(time))
                .forEach(entry -> partMap.put(Time.intersection(entry.getKey(), time), entry.getValue().copy()));
        return new TimeDS(partMap);
    }

    public TimeDS union(TimeDS other) {
        return TimeDS.union(this, other, false);
    }

    public TimeDS union(TimeDS other, boolean doExplanation) {
        return TimeDS.union(this, other, doExplanation);
    }

    public static TimeDS union(TimeDS timeDS_1, TimeDS timeDS_2) {
        return TimeDS.union(timeDS_1, timeDS_2, false);
    }

    public static TimeDS union(TimeDS timeDS_1, TimeDS timeDS_2, boolean doExplanation) {
        TimeDS result = TimeDS.empty();
        Time time1, time2, intersection;
        DependencySet ds1, ds2;

        for (Map.Entry<Time, DependencySet> entry1 : timeDS_1.map.entrySet()) {
            time1 = entry1.getKey();
            ds1 = entry1.getValue();
            for (Map.Entry<Time, DependencySet> entry2 : timeDS_2.map.entrySet()) {
                time2 = entry2.getKey();
                ds2 = entry2.getValue();

                intersection = Time.intersection(time1, time2);
                if (!intersection.isEmpty()) {
                    result.map.put(intersection, ds1.union(ds2, doExplanation));
                }
            }
        }

        result.add(timeDS_1.copy(), false);
        result.add(timeDS_2.copy(), false);

        return result;
    }

    public boolean isEmpty() {
        return map.isEmpty();
    }

    public void addExplain(DependencySet from, boolean doExplanation) {
        if (doExplanation) {
            map.values().forEach(ds -> ds.explain.addAll(from.explain));
        }
    }

    public static TimeDS intersection(TimeDS a, TimeDS b, boolean doExplanation) {
        if (a == null || b == null) {
            return TimeDS.empty();
        }
        Time intersection = Time.intersection(a.time(), b.time());
        return union(a.partBy(intersection), b.partBy(intersection), doExplanation);
    }

    public static TimeDS intersection(TimeDS ...sets) {
        return TimeDS.intersection(false, sets);
    }

    public static TimeDS intersection(boolean doExplanation, TimeDS ...sets) {
        if (Arrays.stream(sets).anyMatch(Objects::isNull)) {
            return TimeDS.empty();
        }
        Time intersection = Time.intersection(Arrays.stream(sets).map(TimeDS::time).toArray(Time[]::new));
        TimeDS result = sets[0].partBy(intersection);
        for (int i = 1; i < sets.length; i++) {
            result = TimeDS.union(result, sets[i].partBy(intersection), doExplanation);
        }
        return  result;
    }

    public static TimeDS clash(TimeDS a, TimeDS b, boolean doExplanation) {
        return intersection(a, b, doExplanation);
    }

    boolean restoredToRemove = false;

    public boolean restoreByBranch(int branch, Time time) {
        if (restoredToRemove) {
            return true;
        }
        Time intersection = Time.intersection(partByBranch(branch).time(), time);
        if (!intersection.isEmpty()) {
            subtract(intersection);
            if (isEmpty()) {
                restoredToRemove = true;
            }
            return true;
        }
        return false;
    }

    public boolean restoreByMax(int max, Time time) {
        if (restoredToRemove) {
            return true;
        }
        Time intersection = Time.intersection(partByMax(max).time(), time);
        if (!intersection.isEmpty()) {
            subtract(intersection);
            if (isEmpty()) {
                restoredToRemove = true;
            }
            return true;
        }
        return false;
    }

    public TimeDS partByBranch(int branch) {
        TreeMap<Time, DependencySet> newMap = new TreeMap<>();
        map.entrySet().stream().filter(e -> e.getValue().getBranch() > branch).forEach(e -> newMap.put(e.getKey(), e.getValue()));
        return new TimeDS(newMap);
    }

    public TimeDS partByMax(int branch) {
        TreeMap<Time, DependencySet> newMap = new TreeMap<>();
        map.entrySet().stream().filter(e -> e.getValue().max() >= branch).forEach(e -> newMap.put(e.getKey(), e.getValue()));
        return new TimeDS(newMap);
    }

    public void reset() {
        map.entrySet().removeIf(e->e.getValue().getBranch() != DependencySet.NO_BRANCH);
    }


    public void unite(DependencySet ds, boolean doExplanation) {
        map.replaceAll((t,d)->d.union(ds, doExplanation));
    }

    public void unite(DependencySet ds) {
        unite(ds, false);
    }

    public TimeDS union(DependencySet ds, boolean doExplanation) {
        TimeDS result = copy();
        result.unite(ds, doExplanation);
        return result;
    }

    public Set<Integer> maxBranches() {
        return map.values().stream().map(DependencySet::max).collect(Collectors.toCollection(TreeSet::new));
    }


    public void subtract(Time time) {
        map.keySet().forEach(t->t.subtract(time));
        map.entrySet().removeIf(entry -> entry.getKey().isEmpty());
    }

    public boolean depends(int branch) {
        return map.values().stream().allMatch(ds -> ds.contains(branch));
    }

    @Override
    public String toString() {
        if (PelletOptions.SPECIAL_LOGS) {
            assert size() == 1;
            return ds().toString();
        }
        StringBuilder sb = new StringBuilder();
        map.forEach((t,ds) -> sb.append(String.format("%s:%s  ", t.toString(), ds.toString())));
        return sb.toString();
    }

    public void setBranch(int branch) {
        map.replaceAll((t,ds)->ds.copy(branch));
    }


//   -------------------------- DS functions -------------------------------------------------------------------------------------------------

    public void add(int b) {
        map.values().forEach(ds -> ds.add(b));
    }

    public boolean contains(int branch) {
        return map.values().stream().allMatch(ds -> ds.contains(branch));
    }

    public boolean isIndependent() {
        return map.values().stream().allMatch(DependencySet::isIndependent);
    }

    public void remove(int branch) {
        map.values().forEach(ds -> ds.remove(branch));
    }

    public TimeDS cache() {
        map.values().forEach(DependencySet::cache);
        return this;
    }

    public int max() {
        return map.values().stream().map(DependencySet::max).max(Integer::compare).get();
    }

    public int getBranch() {
        return map.values().stream().map(DependencySet::getBranch).max(Integer::compare).get();
    }

    public Set<ATermAppl> getExplain() {
        return map.values().stream().map(DependencySet::getExplain).flatMap(Collection::stream).collect(Collectors.toSet());
    }

    public TimeDS copy(int newBranch) {
        TimeDS copy = this.copy();
        copy.map.replaceAll((t,ds)->ds.copy(newBranch));
        return copy;
    }

}
