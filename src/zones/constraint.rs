use std::{cmp::Ordering, fmt, u16};

// The unique index of a clock. This can be used to directly address the DBM.
#[derive(PartialEq, Debug)]
pub struct Clock(u16);

// The zero'th (0) clock is the reference clock and marker of inconsistency.
const REFERENCE: Clock = Clock(0);

pub const fn new_clock(clock: u16) -> Clock {
    Clock(clock)
}

impl Into<u16> for Clock {
    fn into(self) -> u16 {
        return self.0
    }
}

impl From<u16> for Clock {
    fn from(value: u16) -> Self {
        return Self(value)
    }
}

impl fmt::Display for Clock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// Describes the strictness (<, <=) of the constraint between two clocks in the DBM.
#[derive(PartialEq, Debug)]
pub struct Strictness(bool);
const STRICT: Strictness = Strictness(false);
const WEAK: Strictness = Strictness(true);

impl fmt::Display for Strictness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            STRICT => write!(f, "<"),
            WEAK => write!(f, "≤"),
        }
    }
}

// An element optimized for caching which represents a strict or weak
// relation between two clocks (c0 - c1 RELATION). This encoding uses
// the least significant bit to represent the strictness and the other
// bits as the limit. The encoding is [limit] [1 bit strictness].
#[derive(PartialEq, Debug)]
pub struct Relation(i16);

// The minimum possible limit the relation supports is an i15 minimum equivalent.
const MIN_LIMIT: i16 = -16384;
// The maximum possible limit the relation supports is an i15 maximum equivalent.
const MAX_LIMIT: i16 = 16383;

// Inifity is all 1's (Max unsigned bit representation) this is the same as (∞, ≤).
const INFINITY: Relation = new_relation(MAX_LIMIT, WEAK);
// Zero is just a relation with limit of 0 but it is weak and thereby includes 0 (0, ≤).
const ZERO: Relation = new_relation(0, WEAK);

pub const fn new_relation(limit: i16, strictness: Strictness) -> Relation {
    Relation((limit << 1) | strictness.0 as i16)
}

impl Relation {
    // Returns the limit of the relation which can be
    // represented with one less bit than the relation
    // as the last bit describes the relation's strictness.
    pub const fn limit(&self) -> i16 {
        self.0 >> 1
    }

    // Returns the strictness of the relation.
    pub const fn strictness(&self) -> Strictness {
        if self.is_strict() {
            return STRICT;
        }
        return WEAK;
    }

    // Returns true if the strictness of the relation is strict.
    pub const fn is_strict(&self) -> bool {
        (self.0 & 1) == 0
    }

    // Returns true if the strictness of the relation is weak.
    pub const fn is_weak(&self) -> bool {
        return !self.is_strict();
    }

    // Returns true if the relation represents a infinite relation (∞, ≤).
    pub const fn is_infinity(&self) -> bool {
        self.0 == INFINITY.0
    }

    // Returns true if the relation represents a zero relation (0, ≤).
    pub const fn is_zero(&self) -> bool {
        self.0 == ZERO.0
    }

    // If the relation is (0, <) then it can never be true.
    pub const fn is_contradition(&self) -> bool {
        self.limit() == MIN_LIMIT && self.is_strict()
    }
}

impl PartialOrd for Relation {
    fn lt(&self, other: &Self) -> bool {
        self.0 < other.0
    }

    fn gt(&self, other: &Self) -> bool {
        self.0 > other.0
    }

    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        if self.lt(other) {
            return Some(Ordering::Less);
        } else if self.gt(other) {
            return Some(Ordering::Greater);
        }
        Some(Ordering::Equal)
    }
}

impl fmt::Display for Relation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_infinity() {
            return write!(f, "(∞, {})", self.strictness());
        }
        write!(f, "({}, {})", self.limit(), self.strictness())
    }
}

pub struct Constraint {
    lhs: Clock,
    rhs: Clock,
    relation: Relation,
}

pub const fn new_constraint(lhs: Clock, rhs: Clock, relation: Relation) -> Constraint {
    Constraint {
        lhs: lhs,
        rhs: rhs,
        relation: relation,
    }
}

impl  fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} - {} {}", self.lhs, self.rhs, self.relation)
    }
}

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    #[test]
    fn reference_clock_is_zero() {
        assert_eq!(Clock(0), REFERENCE)
    }

    #[test]
    fn strict_is_true() {
        assert_eq!(Strictness(false), STRICT)
    }

    #[test]
    fn weak_is_false() {
        assert_eq!(Strictness(true), WEAK)
    }

    #[test]
    fn weak_formatted_is_less_than_or_equal() {
        assert_eq!("≤", WEAK.to_string())
    }

    #[test]
    fn strict_formatted_is_less_than() {
        assert_eq!("<", STRICT.to_string())
    }

    #[test]
    fn new_relation_returns_correct_strictness() {
        assert_eq!(WEAK, new_relation(0, WEAK).strictness());
        assert_eq!(STRICT, new_relation(0, STRICT).strictness());
        assert_eq!(WEAK, new_relation(i16::MAX, WEAK).strictness());
        assert_eq!(STRICT, new_relation(i16::MAX, STRICT).strictness());
    }

    #[test]
    fn new_relation_returns_correct_limit() {
        assert_eq!(0, new_relation(0, WEAK).limit());
        assert_eq!(10, new_relation(10, WEAK).limit());
        assert_eq!(-10, new_relation(-10, WEAK).limit());
        assert_eq!(-16384, new_relation(-16384, WEAK).limit());
        assert_eq!(16383, new_relation(16383, WEAK).limit());

        let mut rng = rand::thread_rng();
        for _ in 0..10_000 {
            let limit = rng.gen_range(-16384..=16383);
            let relation = new_relation(limit, WEAK);
            assert_eq!(limit, relation.limit())
        }
    }

    #[test]
    fn inifinity() {
        assert_eq!(MAX_LIMIT, INFINITY.limit());
        assert_eq!(WEAK, INFINITY.strictness());
        assert_eq!("(∞, ≤)", INFINITY.to_string());
        assert!(INFINITY.is_infinity());
    }

    #[test]
    fn zero() {
        assert_eq!(0, ZERO.limit());
        assert_eq!(WEAK, ZERO.strictness());
        assert_eq!("(0, ≤)", ZERO.to_string());
        assert!(ZERO.is_zero())
    }

    #[test]
    fn relation_partial_equality() {
        assert_eq!(new_relation(10, WEAK), new_relation(10, WEAK));
        assert_ne!(new_relation(10, STRICT), new_relation(10, WEAK));
        assert_eq!(INFINITY, INFINITY);
        assert_eq!(ZERO, ZERO);
    }

    #[test]
    fn relation_partial_order() {
        struct Case {
            lhs: Relation,
            rhs: Relation,
            ordering: Ordering,
        }
        let cases: [Case; 5] = [
            Case {
                lhs: new_relation(10, WEAK),
                rhs: new_relation(10, WEAK),
                ordering: Ordering::Equal,
            },
            Case {
                lhs: new_relation(10, STRICT),
                rhs: new_relation(10, WEAK),
                ordering: Ordering::Less,
            },
            Case {
                lhs: new_relation(10, WEAK),
                rhs: new_relation(10, STRICT),
                ordering: Ordering::Greater,
            },
            Case {
                lhs: INFINITY,
                rhs: new_relation(10, STRICT),
                ordering: Ordering::Greater,
            },
            Case {
                lhs: new_relation(10, WEAK),
                rhs: INFINITY,
                ordering: Ordering::Less,
            },
        ];

        for case in cases {
            match case.ordering {
                Ordering::Equal => assert_eq!(
                    case.ordering,
                    case.lhs.partial_cmp(&case.rhs).unwrap(),
                    "{} == {}",
                    case.lhs,
                    case.rhs
                ),
                Ordering::Less => assert_eq!(
                    case.ordering,
                    case.lhs.partial_cmp(&case.rhs).unwrap(),
                    "{} < {}",
                    case.lhs,
                    case.rhs
                ),
                Ordering::Greater => assert_eq!(
                    case.ordering,
                    case.lhs.partial_cmp(&case.rhs).unwrap(),
                    "{} > {}",
                    case.lhs,
                    case.rhs
                ),
            }
        }
    }

    #[test]
    fn constraint_display() {
        assert_eq!("0 - 0 (0, ≤)", new_constraint(REFERENCE, REFERENCE, new_relation(0, WEAK)).to_string());
        assert_eq!("0 - 2 (0, ≤)", new_constraint(REFERENCE, new_clock(2), new_relation(0, WEAK)).to_string());
    }
}
