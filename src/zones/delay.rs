/*Delay fix:
Ask youself the question what is the delay from (5, <) to (10, <=)?
If is not 5 because that would yield (10, <) and not reach the bound.
Instead a delay is not a relation but a seperate type: Which can
describe a delay d +/- epsilon and thereby either relax or make
strictness more strict.

(5, <)	(10, <)	cross 5, stay below 10		+ε
(5, <=)	(10, <=)	no strictness crossing	Exact (no ε)
(5, <=)	(10, <)	stay below 10 strictly		-ε
(5, <)	(10, <=)	cross strict at 5	+ε

What happens when we add +ε to (5, <=)?

    The upper bound (<=) will increase by d + ε, but the strictness remains non-strict (<=), because you're allowing for a slight relaxation, not a tightening.

    So, (5, <=) delayed by 5 + ε should result in (10, <=) — the relation remains non-strict.*/

use std::{cmp::Ordering, ops::Add};

use super::constraint::{Limit, Relation, Strictness};

/// Represents a delay applied to a relation in a Difference Bound Matrix (DBM).
///
/// # Examples
///
/// ```rust
/// let exact = Delay::exact(5);       // 5 time units, no change in strictness
/// let relaxed = Delay::relax(5);     // 5 time units + ε, relax strict bounds
/// let tightened = Delay::tighten(5); // 5 time units - ε, tighten non-strict bounds
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum Delay {
    /// Delay by exactly `d` units without changing constraint strictness.
    ///
    /// No ε adjustment (`+ε` or `-ε`).
    Exact(Limit),

    /// Delay by `d` units and relax strict constraints (`<` becomes `<=`).
    ///
    /// Conceptually represents `d + ε`.
    Relaxed(Limit),

    /// Delay by `d` units and tighten non-strict constraints (`<=` becomes `<`).
    ///
    /// Conceptually represents `d - ε`.
    Tightened(Limit),
}

/// Represents a delay with possible semantic variations: exact, relaxed (+ε), or tightened (−ε).
/// 
/// This implementation provides constructors, type checks, and access to the underlying limit.
impl Delay {
    /// Constructs an exact delay.
    pub const fn exact(limit: Limit) -> Self {
        Self::Exact(limit)
    }

    /// Constructs a relaxed delay (interpreted as `limit + ε`).
    pub const fn relax(limit: Limit) -> Self {
        Self::Relaxed(limit)
    }

    /// Constructs a tightened delay (interpreted as `limit − ε`).
    pub const fn tighten(limit: Limit) -> Self {
        Self::Tightened(limit)
    }

    /// Returns `true` if the delay is exact.
    pub const fn is_exact(&self) -> bool {
        matches!(self, Delay::Exact(_))
    }

    /// Returns `true` if the delay is relaxed (`+ε`).
    pub const fn is_relaxed(&self) -> bool {
        matches!(self, Delay::Relaxed(_))
    }

    /// Returns `true` if the delay is tightened (`−ε`).
    pub const fn is_tightened(&self) -> bool {
        matches!(self, Delay::Tightened(_))
    }

    /// Returns the numerical component of the delay.
    pub const fn limit(&self) -> Limit {
        match self {
            Delay::Exact(limit) | Delay::Relaxed(limit) | Delay::Tightened(limit) => *limit,
        }
    }

    /// Applies this delay to a clock constraint, producing a new relation.
    ///
    /// This is typically used to compute the effect of time progression on
    /// upper bounds in DBMs. The delay adjusts the limit and may alter the
    /// strictness depending on its variant (`Relaxed`, `Tightened`, or `Exact`).
    pub fn delay_relation(&self, relation: Relation) -> Relation {
        let limit = self.limit() + relation.limit();
        let strictness = match self {
            Delay::Exact(_) => relation.strictness(),
            Delay::Relaxed(_) => Strictness::Weak,
            Delay::Tightened(_) => Strictness::Strict,
        };
        Relation::new(limit, strictness)
    }
}

impl Ord for Delay {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let limit_cmp = self.limit().cmp(&other.limit());

        if limit_cmp != Ordering::Equal {
            return limit_cmp;
        }

        // If limits are the same, compare based on the strictness
        match (self, other) {
            (Delay::Exact(_), Delay::Exact(_)) => Ordering::Equal,
            (Delay::Exact(_), Delay::Relaxed(_)) => Ordering::Less,
            (Delay::Exact(_), Delay::Tightened(_)) => Ordering::Greater,
            (Delay::Relaxed(_), Delay::Exact(_)) => Ordering::Greater,
            (Delay::Tightened(_), Delay::Exact(_)) => Ordering::Less,

            (Delay::Relaxed(_), Delay::Relaxed(_)) => Ordering::Equal,
            (Delay::Relaxed(_), Delay::Tightened(_)) => Ordering::Greater,
            (Delay::Tightened(_), Delay::Relaxed(_)) => Ordering::Less,

            (Delay::Tightened(_), Delay::Tightened(_)) => Ordering::Equal,
        }
    }
}

impl Add<Relation> for Delay {
    type Output = Relation;

    fn add(self, rhs: Relation) -> Self::Output {
        self.delay_relation(rhs)
    }
}

#[cfg(test)]
mod tests {
    use crate::zones::delay::Delay;

    #[test]
    fn delay_limit() {
        assert_eq!(123, Delay::exact(123).limit());
        assert_eq!(123, Delay::relax(123).limit());
        assert_eq!(123, Delay::tighten(123).limit());
        assert_eq!(-123, Delay::exact(-123).limit());
        assert_eq!(-123, Delay::relax(-123).limit());
        assert_eq!(-123, Delay::tighten(-123).limit());
    }

    #[test]
    fn delay_type() {
        assert!(Delay::exact(1).is_exact());
        assert!(!Delay::relax(1).is_exact());
        assert!(!Delay::tighten(1).is_exact());
        assert!(!Delay::exact(1).is_relaxed());
        assert!(Delay::relax(1).is_relaxed());
        assert!(!Delay::tighten(1).is_relaxed());
        assert!(!Delay::exact(1).is_tightened());
        assert!(!Delay::relax(1).is_tightened());
        assert!(Delay::tighten(1).is_tightened());
    }

    #[test]
    fn delay_relation() {

    }

    #[test]
    fn delay_order() {
        let exact = Delay::exact(5);
        let relaxed = Delay::relax(5);
        let tightened = Delay::tighten(5);

        assert!(exact == exact);
        assert!(relaxed == relaxed);
        assert!(tightened == tightened);
        assert!(exact < relaxed);
        assert!(exact > tightened);
        assert!(relaxed > exact);
        assert!(tightened < exact);
        assert!(relaxed > tightened);
        assert!(tightened < relaxed);
    }
}