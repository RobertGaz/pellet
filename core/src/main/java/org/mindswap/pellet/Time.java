package org.mindswap.pellet;

import javax.annotation.Nonnull;
import java.util.AbstractMap;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

public class Time implements Iterable<Period>,  Comparable<Time> {
    private Set<Period> periods = new TreeSet<>();
//    private TreeSet<Long> start = new TreeSet<>();
//    private TreeSet<Long> end = new TreeSet<>();

    public Time() {}
    public Time(Period period) {
        if (period != null) {
            addPeriod(period);
        }
    }
    public Time(Set<Period> periods) {
        periods.forEach(this::addPeriod);
    }
    public Time(Time other) {
        if (other != null) {
            periods = other.periods.stream().map(Period::new).collect(Collectors.toCollection(TreeSet::new));
        }
    }
    public static Time universal() {
        return new Time(new Period(null, null));
    }
    public static Time empty() {
        return new Time();
    }
    public Time copy() {
        return new Time(this);
    }

    public void addPeriod(Period newPeriod) {
        if (newPeriod != null) {
            for (Iterator<Period> iterator = iterator(); iterator.hasNext(); ) {
                Period period = iterator.next();
                if (newPeriod.equals(period)) {
                    return;
                }
                if (newPeriod.intersects(period)) {
                    newPeriod = Period.union(newPeriod, period);
                    iterator.remove();
                }
            }
            periods.add(newPeriod);
//        start.add(newPeriod.getStart() == null ? 0 : newPeriod.getStart());
//        end.add(newPeriod.getEnd() == null ? Long.MAX_VALUE : newPeriod.getEnd());
        }
    }


    public boolean inside(Time other) {
        if (other == null) {
            return false;
        }

        return intersection(this, other).equals(this);
    }

    public boolean intersects(Time other) {
        if (other == null) {
            return false;
        }
        for (Period a : periods) {
            for (Period b : other.getPeriods()) {
                if (a.intersection(b) != null) {
                    return true;
                }
            }
        }

        return false;
    }

    public static Time union(Time ...times) {
        Time result = new Time(times[0]);
        for (int i = 1; i < times.length && !result.isEmpty(); i++) {
            if (times[i] != null) {
                result.unite(times[i]);
            }
        }
        return result;
    }

    public static Time intersection(Time ...times) {
        if (Arrays.stream(times).anyMatch(Objects::isNull)) {
            return Time.empty();
        }
        Time result = times[0].copy();
        for (int i = 1; i < times.length && !result.isEmpty(); i++) {
            result.intersect(times[i]);
        }
        return result;
    }

    public void intersect(Time other) {
        if (other != null) {
            Time result = new Time();
            for (Period a : periods) {
                for (Period b : other.getPeriods()) {
                    Period intersection = a.intersection(b);
                    if (intersection != null) {
                        result.addPeriod(intersection);
                    }
                }
            }
            periods = result.getPeriods();
        }
    }

    public void unite(Time other) {
        if (other != null) {
            for (Period period : other.getPeriods()) {
                addPeriod(period);
            }
        }
    }

    public static Time subtraction(Time first, Time second) {
        Time a = new Time(first);

        a.subtract(second);
        return a;
    }

//    public static Triple<Time, Time, Time> split(Time first, Time second) {
//        Time firstPart = subtraction(first, second);
//        if (firstPart.isEmpty()) {
//            return new Triple<Time, Time, Time>();
//        }
//        Time intersection = intersection(first, second);
//
//        if (intersection.isEmpty()) {
//            result.map.put(intersection, entry1.getValue().union(entry2.getValue(), doExplanation));
//
//            part = Time.subtraction(time1, time2);
//            if (!part.isEmpty()) {
//                result.map.put(part, entry1.getValue());
//                result.map.put(Time.subtraction(time2, time1), entry2.getValue());
//            }
//        }
//    }

    public void subtract(Time other) {
        if (other != null) {
            other.forEach(this::subtractPeriod);
        }
    }

    protected Time subtractPeriod(Period period) {
        if (period == null) {
            return this;
        }
        Set<Period> toRemove = new TreeSet<Period>();
        Set<Period> toAdd = new TreeSet<>();
        Time subtracted = new Time();

        for (Period knownPeriod : periods) {
            if (period.equals(knownPeriod)) {
                toRemove.add(knownPeriod);
                break;
            }

            Period intersection = period.intersection(knownPeriod);
            if (intersection == null) {
                continue;
            }

            toRemove.add(knownPeriod);

            if (intersection.equals(knownPeriod)) {
                continue;
            }

            if (intersection.startsLater(knownPeriod)) {
                toAdd.add(new Period(knownPeriod.getStart(), intersection.getStart()));
            }

            if (intersection.endsEarlier(knownPeriod)) {
                toAdd.add(new Period(intersection.getEnd(), knownPeriod.getEnd()));
            }
            subtracted.addPeriod(intersection);
        }

        periods.removeAll(toRemove);
        periods.addAll(toAdd);
        return subtracted;
    }



    public Set<Period> getPeriods() {
        return periods;
    }

    public boolean isUniversal() {
        return periods.stream().anyMatch(Period::isUniversal);
    }

    public boolean isEmpty() {
        return periods == null || periods.isEmpty();
    }

    @Override
    public int compareTo(@Nonnull Time other) {
        if (isEmpty() && other.isEmpty() || isUniversal() && other.isUniversal()) {
            return 0;
        }
        return ((TreeSet<Period>)periods).first().compareTo(((TreeSet<Period>)other.periods).first());
    }


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (periods.size() != 1) {
            sb.append("(");
        }
        for (Period period : periods) {
            sb.append(period);
            sb.append(" ");
        }
        sb.deleteCharAt(sb.length()-1);
        if (periods.size() > 1) {
            sb.append(")");
        }
        return sb.toString();
    }

    @Nonnull
    public Iterator<Period> iterator() {
        return periods.iterator();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Time time = (Time) o;
        return periods.equals(time.periods);
    }

    @Override
    public int hashCode() {
        return Objects.hash(periods);
    }



    public static boolean isCardExceeded(List<Time> times, int max) {
        for (Time a : times) {
            Time currentIntersection = a;
            int currentCard = 0;
            for (Time b : times) {
                if (a != b) {
                    Time intersection = Time.intersection(currentIntersection, b);
                    if (!intersection.isEmpty()) {
                        currentIntersection = intersection;
                        currentCard++;

                        if (currentCard > max) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }


    public static <T> Map.Entry<Time, Set<T>> getCardExceedEntry(Map<T, Time> map, int max) {
        Set<Map.Entry<T, Time>> entrySet = map.entrySet();

        for (Map.Entry<T, Time> a : entrySet) {
            Time currentIntersection = a.getValue();
            Set<T> currentNodes = new LinkedHashSet<>(Arrays.asList(a.getKey()));
            for (Map.Entry<T, Time> b : map.entrySet()) {
                if (a != b) {
                    Time intersection = Time.intersection(currentIntersection, b.getValue());
                    if (!intersection.isEmpty()) {
                        currentIntersection = intersection;
                        currentNodes.add(b.getKey());
                    }
                }
            }
            if (currentNodes.size() > max) {
                return new AbstractMap.SimpleEntry<>(currentIntersection, currentNodes);
            }
        }
        return null;
    }
}

