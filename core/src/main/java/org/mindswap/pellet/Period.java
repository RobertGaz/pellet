package org.mindswap.pellet;

import java.util.Objects;

public class Period implements Comparable<Period> {
    private Long start;
    private Long end;

    public Period(Long start, Long end) {
        this.start = start;
        this.end = end;
    }

    public Period(Period other) {
        start = other.start;
        end = other.end;
    }

    public boolean isUniversal() {
        if (start == null && end == null) {
            return true;
        } else {
            return false;
        }
    }

    public static Period union(Period a, Period b) {
        Long start = (a.start == null || b.start == null) ? null : Math.min(a.start, b.start);
        Long end = (a.end == null || b.end == null) ? null : Math.max(a.end, b.end);
        return new Period(start, end);
    }

    public boolean startsEarlier(Period other) {
        if (start == null && other.start == null) {
            return false;
        }
        if (start == null) {
            return true;
        }
        if (other.start == null) {
            return false;
        }
        return start < other.start;
    }

    public boolean startsLater(Period other) {
        return other.startsEarlier(this);
    }

    public boolean endsEarlier(Period other) {
        if (end == null && other.end == null) {
            return false;
        }
        if (end == null) {
            return false;
        }
        if (other.end == null) {
            return true;
        }
        return end < other.end;
    }

    public boolean endsLater(Period other) {
        return other.endsEarlier(this);
    }

//    ROBERT оптимизировать
    public boolean intersects(Period other) {
        return intersection(other) != null;
    }

    public Period intersection(Period other) {
        if (start == null && end == null) {
            return other;
        }
        if (other.start == null && other.end == null) {
            return this;
        }


        if (start == null && other.end == null) {
            if (end > other.start) {
                return new Period(other.start, end);
            } else {
                return null;
            }
        }

        if (other.start == null && end == null) {
            if (other.end > start) {
                return new Period(start, other.end);
            } else {
                return null;
            }
        }

        if (start == null && other.start == null) {
            return new Period(null, Math.min(end, other.end));
        }

        if (end == null && other.end == null) {
            return new Period(Math.max(start, other.start), null);
        }

        if (start == null) {
            if (end <= other.start) {
                return null;
            }
            if (end >= other.end) {
                return other;
            }
            return new Period(other.start, end);
        }

        if (other.start == null) {
            if (other.end <= start) {
                return null;
            }
            if (other.end >= end) {
                return this;
            }
            return new Period(start, other.end);
        }

        if (end == null) {
            if (start >= other.end) {
                return null;
            }
            if (start <= other.start) {
                return other;
            }
            return new Period(start, other.end);
        }

        if (other.end == null) {
            if (other.start >= end) {
                return null;
            }
            if (other.start <= start) {
                return this;
            }
            return new Period(other.start, end);
        }

        if (start >= other.start && start < other.end) {
            return new Period(start, Math.min(end, other.end ));
        }

        if (other.start >= start && other.start < end) {
            return new Period(other.start, Math.min(end, other.end ));
        }
        return null;
    }

    @Override
    public int compareTo(Period other) {
        if (start == other.start) {
            if (end == other.end) {
                return 0;
            }
            if (end == null) {
                return 1;
            }
            if (other.end == null) {
                return -1;
            }
            return end.compareTo(other.end);
        }
        if (start == null) {
            return -1;
        }
        if (other.start == null) {
            return 1;
        }

        return start.compareTo(other.getStart());
    }

    public Long getEnd() {
        return end;
    }

    public void setEnd(Long end) {
        this.end = end;
    }

    public Long getStart() {
        return start;
    }

    public void setStart(Long start) {
        this.start = start;
    }

    public String toString() {
        return "["+start+","+end+")";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Period period = (Period) o;
        return Objects.equals(start, period.start) &&
                Objects.equals(end, period.end);
    }

    @Override
    public int hashCode() {
        return Objects.hash(start, end);
    }
}
