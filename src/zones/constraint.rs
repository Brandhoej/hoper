use std::{
    cmp::Ordering,
    fmt,
    ops::{Add, Sub},
    u16,
};

use rand::{
    distributions::{Standard, Uniform},
    prelude::Distribution,
    Rng,
};

/// The unique index of a clock. This can be used to directly address the DBM.
pub type Clock = u16;

/// The zero'th (0) clock is the reference clock and marker of inconsistency.
pub const REFERENCE: Clock = 0;

/// Describes the strictness (<, <=) of the constraint between two clocks in the DBM.
#[derive(PartialEq, Debug)]
pub enum Strictness {
    Strict,
    Weak,
}

impl Strictness {
    pub const fn opposite(&self) -> Self {
        match self {
            Strictness::Strict => Strictness::Weak,
            Strictness::Weak => Strictness::Strict,
        }
    }
}

impl Distribution<Strictness> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Strictness {
        if rng.gen_bool(1.0 / 2.0) {
            return Strictness::Strict;
        }
        Strictness::Weak
    }
}

impl fmt::Display for Strictness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Strictness::Strict => write!(f, "<"),
            Strictness::Weak => write!(f, "≤"),
        }
    }
}

pub type Limit = i16;

/// An element optimized for caching which represents a strict or weak
/// relation between two clocks (c0 - c1 RELATION). This encoding uses
/// the least significant bit to represent the strictness and the other
/// bits as the limit. The encoding is [limit] [1 bit strictness].
#[derive(PartialEq, Debug, Clone)]
pub struct Relation(Limit);

/// The minimum possible limit the relation supports is an i15 minimum equivalent.
pub const MIN_LIMIT: Limit = -16384;
/// The maximum possible limit the relation supports is an i15 maximum equivalent.
pub const MAX_LIMIT: Limit = 16383;

/// Inifity is all 1's (Max unsigned bit representation) this is the same as (∞, ≤).
pub const INFINITY: Relation = Relation::new(MAX_LIMIT, Strictness::Weak);
/// Zero is just a relation with limit of 0 but it is weak and thereby includes 0 (0, ≤).
pub const ZERO: Relation = Relation::new(0, Strictness::Weak);

impl Relation {
    pub const fn new(limit: Limit, strictness: Strictness) -> Self {
        let strictness_bit = match strictness {
            Strictness::Strict => 0,
            Strictness::Weak => 1,
        };
        Self((limit << 1) | strictness_bit)
    }

    /// Returns the limit of the relation which can be
    /// represented with one less bit than the relation
    /// as the last bit describes the relation's strictness.
    pub const fn limit(&self) -> Limit {
        self.0 >> 1
    }

    /// Returns the strictness of the relation.
    pub const fn strictness(&self) -> Strictness {
        if self.is_strict() {
            return Strictness::Strict;
        }
        return Strictness::Weak;
    }

    pub const fn as_weak(&self) -> Self {
        Self::new(self.limit(), Strictness::Weak)
    }

    pub const fn as_strict(&self) -> Self {
        Self::new(self.limit(), Strictness::Strict)
    }

    /// Returns true if the strictness of the relation is strict.
    pub const fn is_strict(&self) -> bool {
        (self.0 & 1) == 0
    }

    /// Returns true if the strictness of the relation is weak.
    pub const fn is_weak(&self) -> bool {
        return !self.is_strict();
    }

    /// Returns true if the relation represents a infinite relation (∞, ≤).
    pub const fn is_infinity(&self) -> bool {
        self.0 == INFINITY.0
    }

    /// Returns true if the relation represents a zero relation (0, ≤).
    pub const fn is_zero(&self) -> bool {
        self.0 == ZERO.0
    }

    /// If the relation is (0, <) then it can never be true.
    pub const fn is_contradition(&self) -> bool {
        self.limit() == MIN_LIMIT && self.is_strict()
    }

    /// Negates the relation and returns self.
    pub const fn negation(&self) -> Self {
        Self::new(-self.limit(), self.strictness().opposite())
    }

    /// Returns the sum of two constraints. The sum is satisfies both original constraints (lhs/rhs).
    /// In other words, it does not allow any behavior that violates either of the
    /// original constraints. to ensure that the sum captures the intersection of the
    /// original constraints accurately, we choose the tightest or most restrictive
    /// relation that satisfies both original constraints. This ensures that the
    /// resulting constraint is as tight as possible while still being consistent
    /// with the original constraints. Thereby, if one relation is ≤ (i.e., 1)
    /// then it is keps over < (i.e., 0). Addition does not handle overflows, and
    /// therefore yeilds undefined behaviour.
    /// This addition is mostly used to compute the accumulated path when closing a DBM.
    pub const fn addition(&self, other: &Self) -> Self {
        if self.is_infinity() || other.is_infinity() {
            return INFINITY;
        }

        // First adding the lhs and rhs increases the limit.
        // Then we ensure the tightest constraint that satisfies both constraints is kept.
        Self((self.0 + other.0) - ((self.0 | other.0) & 1))
    }

    /// subtract other from self by "self + (-other)".
    pub const fn subtract(&self, other: &Self) -> Self {
        self.addition(&other.negation())
    }
}

impl Distribution<Relation> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Relation {
        let strictness: Strictness = rng.gen();
        let limit: Limit = rng.gen_range(MIN_LIMIT..=MAX_LIMIT);
        Relation::new(limit, strictness)
    }
}

impl Add for Relation {
    type Output = Relation;

    fn add(self, rhs: Self) -> Self::Output {
        self.addition(&rhs)
    }
}

impl Sub for Relation {
    type Output = Relation;

    fn sub(self, rhs: Self) -> Self::Output {
        self.subtract(&rhs)
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

/// Q: Would an enum be better here? Upper, Lower, and Diagonal constraint? Or Straight, and Diagonal constraint?
pub struct Constraint {
    lhs: Clock,
    rhs: Clock,
    relation: Relation,
}

impl Constraint {
    pub const fn new(lhs: Clock, rhs: Clock, relation: Relation) -> Self {
        Self { lhs, rhs, relation }
    }
}

impl fmt::Display for Constraint {
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
        assert_eq!(0, REFERENCE)
    }

    #[test]
    fn weak_formatted_is_less_than_or_equal() {
        assert_eq!("≤", Strictness::Weak.to_string())
    }

    #[test]
    fn strict_formatted_is_less_than() {
        assert_eq!("<", Strictness::Strict.to_string())
    }

    #[test]
    fn new_relation_returns_correct_strictness() {
        assert_eq!(
            Strictness::Weak,
            Relation::new(0, Strictness::Weak).strictness()
        );
        assert_eq!(
            Strictness::Strict,
            Relation::new(0, Strictness::Strict).strictness()
        );
        assert_eq!(
            Strictness::Weak,
            Relation::new(i16::MAX, Strictness::Weak).strictness()
        );
        assert_eq!(
            Strictness::Strict,
            Relation::new(i16::MAX, Strictness::Strict).strictness()
        );
    }

    #[test]
    fn new_relation_returns_correct_limit() {
        assert_eq!(0, Relation::new(0, Strictness::Weak).limit());
        assert_eq!(10, Relation::new(10, Strictness::Weak).limit());
        assert_eq!(-10, Relation::new(-10, Strictness::Weak).limit());
        assert_eq!(-16384, Relation::new(-16384, Strictness::Weak).limit());
        assert_eq!(16383, Relation::new(16383, Strictness::Weak).limit());

        let mut rng = rand::thread_rng();
        for _ in 0..10_000 {
            let limit = rng.gen_range(-16384..=16383);
            let relation = Relation::new(limit, Strictness::Weak);
            assert_eq!(limit, relation.limit())
        }
    }

    #[test]
    fn inifinity() {
        assert_eq!(MAX_LIMIT, INFINITY.limit());
        assert_eq!(Strictness::Weak, INFINITY.strictness());
        assert_eq!("(∞, ≤)", INFINITY.to_string());
        assert!(INFINITY.is_infinity());
    }

    #[test]
    fn zero() {
        assert_eq!(0, ZERO.limit());
        assert_eq!(Strictness::Weak, ZERO.strictness());
        assert_eq!("(0, ≤)", ZERO.to_string());
        assert!(ZERO.is_zero())
    }

    #[test]
    fn relation_partial_equality() {
        assert_eq!(
            Relation::new(10, Strictness::Weak),
            Relation::new(10, Strictness::Weak)
        );
        assert_ne!(
            Relation::new(10, Strictness::Strict),
            Relation::new(10, Strictness::Weak)
        );
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
                lhs: Relation::new(10, Strictness::Weak),
                rhs: Relation::new(10, Strictness::Weak),
                ordering: Ordering::Equal,
            },
            Case {
                lhs: Relation::new(10, Strictness::Strict),
                rhs: Relation::new(10, Strictness::Weak),
                ordering: Ordering::Less,
            },
            Case {
                lhs: Relation::new(10, Strictness::Weak),
                rhs: Relation::new(10, Strictness::Strict),
                ordering: Ordering::Greater,
            },
            Case {
                lhs: INFINITY,
                rhs: Relation::new(10, Strictness::Strict),
                ordering: Ordering::Greater,
            },
            Case {
                lhs: Relation::new(10, Strictness::Weak),
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
        assert_eq!(
            "0 - 0 (0, ≤)",
            Constraint::new(REFERENCE, REFERENCE, Relation::new(0, Strictness::Weak)).to_string()
        );
        assert_eq!(
            "0 - 2 (0, ≤)",
            Constraint::new(REFERENCE, 2, Relation::new(0, Strictness::Weak)).to_string()
        );
    }

    #[test]
    fn relation_negation() {
        assert_eq!(
            "(-10, <)",
            Relation::new(10, Strictness::Weak).negation().to_string()
        )
    }

    #[test]
    fn add_relation() {
        struct Case {
            lhs: Relation,
            rhs: Relation,
            expected: Relation,
        }
        let cases: [Case; 7] = [
            Case {
                lhs: Relation::new(10, Strictness::Weak),
                rhs: Relation::new(10, Strictness::Weak),
                expected: Relation::new(20, Strictness::Weak),
            },
            Case {
                lhs: Relation::new(10, Strictness::Strict),
                rhs: Relation::new(10, Strictness::Weak),
                expected: Relation::new(20, Strictness::Strict),
            },
            Case {
                lhs: Relation::new(10, Strictness::Weak),
                rhs: Relation::new(10, Strictness::Strict),
                expected: Relation::new(20, Strictness::Strict),
            },
            Case {
                lhs: Relation::new(11, Strictness::Weak),
                rhs: Relation::new(10, Strictness::Strict),
                expected: Relation::new(21, Strictness::Strict),
            },
            Case {
                lhs: INFINITY,
                rhs: Relation::new(10, Strictness::Weak),
                expected: INFINITY,
            },
            Case {
                lhs: INFINITY,
                rhs: Relation::new(10, Strictness::Weak),
                expected: INFINITY,
            },
            Case {
                lhs: INFINITY,
                rhs: Relation::new(10, Strictness::Strict),
                expected: INFINITY,
            },
        ];

        for case in cases {
            let actual = case.lhs.clone() + case.rhs.clone();
            assert_eq!(
                case.expected, actual,
                "{} + {} = {}",
                case.lhs, case.rhs, actual
            );
        }
    }
}
