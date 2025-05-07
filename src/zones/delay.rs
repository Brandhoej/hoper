use std::{cmp::Ordering, fmt, ops::Add};

use super::constraint::{Limit, Relation, Strictness};

/// Represents a delay applied to a relation within a Difference Bound Matrix (DBM).
///
/// # Overview
/// A `Delay` is necessary to model the passage of time in DBMs, especially when relaxing or tightening
/// timing constraints. One might wonder why a `Relation` isn't sufficient to express delays.
/// Consider a state where the constraint is `x < 5`, and the location's invariant is `x ≤ 10`.
/// There’s no `Relation` that, when added to `(5, <)`, results in `(10, ≤)` because relation addition
/// always produces the strictest bound of the operands. Thus, `Delay` exists to explicitly model the
/// relaxation (or tightening) of bounds over time.
///
/// # Examples
///
/// ```rust
/// let exact = Delay::exact(5);       // Exactly 5 time units; preserves strictness
/// let relaxed = Delay::relax(5);     // 5 time units ↑; relaxes strict bounds
/// let tightened = Delay::tighten(5); // 5 time units ↓; tightens non-strict bounds
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Delay {
    /// Delay by exactly `d` units without changing constraint strictness.
    ///
    /// No ε adjustment (`↑` or `↓`).
    Exact(Limit),

    /// Delay by `d` units and relax strict constraints (`<` becomes `≤`).
    ///
    /// Conceptually represents `d↑`.
    Relaxed(Limit),

    /// Delay by `d` units and tighten non-strict constraints (`≤` becomes `<`).
    ///
    /// Conceptually represents `d↓`.
    Tightened(Limit),
}

/// Represents a delay with possible semantic variations: exact, relaxed (↑), or tightened (↓).
impl Delay {
    /// Constructs an exact delay.
    pub const fn exact(limit: Limit) -> Self {
        Self::Exact(limit)
    }

    /// Constructs a relaxed delay (interpreted as `limit↑`).
    pub const fn relax(limit: Limit) -> Self {
        Self::Relaxed(limit)
    }

    /// Constructs a tightened delay (interpreted as `limit↓`).
    pub const fn tighten(limit: Limit) -> Self {
        Self::Tightened(limit)
    }

    /// Constructs a delay that represents the delay between `before` and `after`.
    pub fn between(before: Relation, after: Relation) -> Self {
        let limit = after.limit() - before.limit();
        match (before.strictness(), after.strictness()) {
            (Strictness::Strict, Strictness::Strict) => Self::exact(limit),
            (Strictness::Strict, Strictness::Weak) => Self::relax(limit),
            (Strictness::Weak, Strictness::Strict) => Self::tighten(limit),
            (Strictness::Weak, Strictness::Weak) => Self::exact(limit),
        }
    }

    /// Returns `true` if the delay is exact.
    pub const fn is_exact(&self) -> bool {
        matches!(self, Delay::Exact(_))
    }

    /// Returns `true` if the delay is relaxed (`↑`).
    pub const fn is_relaxed(&self) -> bool {
        matches!(self, Delay::Relaxed(_))
    }

    /// Returns `true` if the delay is tightened (`↓`).
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

impl fmt::Display for Delay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Delay::Exact(limit) => write!(f, "{}", limit),
            Delay::Relaxed(limit) => write!(f, "{}↑", limit),
            Delay::Tightened(limit) => write!(f, "{}↓", limit),
        }
    }
}

impl Ord for Delay {
    fn cmp(&self, other: &Self) -> Ordering {
        if self < other {
            Ordering::Less
        } else if self == other {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
}

impl PartialOrd for Delay {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let limit = self.limit().cmp(&other.limit());

        if limit != Ordering::Equal {
            return Some(limit);
        }

        // If limits are the same, compare based on the strictness
        Some(match (self, other) {
            (Delay::Exact(_), Delay::Exact(_)) => Ordering::Equal,
            (Delay::Exact(_), Delay::Relaxed(_)) => Ordering::Less,
            (Delay::Exact(_), Delay::Tightened(_)) => Ordering::Greater,
            (Delay::Relaxed(_), Delay::Exact(_)) => Ordering::Greater,
            (Delay::Tightened(_), Delay::Exact(_)) => Ordering::Less,

            (Delay::Relaxed(_), Delay::Relaxed(_)) => Ordering::Equal,
            (Delay::Relaxed(_), Delay::Tightened(_)) => Ordering::Greater,
            (Delay::Tightened(_), Delay::Relaxed(_)) => Ordering::Less,

            (Delay::Tightened(_), Delay::Tightened(_)) => Ordering::Equal,
        })
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
    use crate::zones::{constraint::Relation, delay::Delay};

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
    fn elapse() {
        assert_eq!("(2, ≤)", (Delay::relax(1) + Relation::weak(1)).to_string());
        assert_eq!("(2, ≤)", (Delay::relax(1) + Relation::strict(1)).to_string());
        assert_eq!("(2, <)", (Delay::tighten(1) + Relation::weak(1)).to_string());
        assert_eq!("(2, <)", (Delay::tighten(1) + Relation::strict(1)).to_string());
        assert_eq!("(2, ≤)", (Delay::exact(1) + Relation::weak(1)).to_string());
        assert_eq!("(2, <)", (Delay::exact(1) + Relation::strict(1)).to_string());

        assert_eq!("(0, ≤)", (Delay::relax(-1) + Relation::weak(1)).to_string());
        assert_eq!("(0, ≤)", (Delay::relax(-1) + Relation::strict(1)).to_string());
        assert_eq!("(0, <)", (Delay::tighten(-1) + Relation::weak(1)).to_string());
        assert_eq!("(0, <)", (Delay::tighten(-1) + Relation::strict(1)).to_string());
        assert_eq!("(0, ≤)", (Delay::exact(-1) + Relation::weak(1)).to_string());
        assert_eq!("(0, <)", (Delay::exact(-1) + Relation::strict(1)).to_string());
    }

    #[test]
    fn between() {
        assert_eq!("", Delay::between(Relation::weak(1), Relation::weak(1)).to_string())
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

    #[test]
    fn delay_relation() {
        // Relations:
        let strict = Relation::strict(5);
        let weak = Relation::weak(5);
        // Delays:
        let exact = Delay::exact(5);
        let relaxed = Delay::relax(5);
        let tightened = Delay::tighten(5);

        assert_eq!("(10, <)", (exact + strict).to_string());
        assert_eq!("(10, ≤)", (relaxed + strict).to_string());
        assert_eq!("(10, <)", (tightened + strict).to_string());

        assert_eq!("(10, ≤)", (exact + weak).to_string());
        assert_eq!("(10, ≤)", (relaxed + weak).to_string());
        assert_eq!("(10, <)", (tightened + weak).to_string());
    }

    #[test]
    fn delay_between() {
        let neg_strict = Relation::strict(-5);
        let neg_weak = Relation::weak(-5);
        let pos_strict = Relation::strict(5);
        let pos_weak = Relation::weak(5);

        assert_eq!("0", Delay::between(neg_strict, neg_strict).to_string());
        assert_eq!("0", Delay::between(neg_weak, neg_weak).to_string());
        assert_eq!("0", Delay::between(pos_strict, pos_strict).to_string());
        assert_eq!("0", Delay::between(pos_weak, pos_weak).to_string());
        
        assert_eq!("10", Delay::between(neg_strict, pos_strict).to_string());
        assert_eq!("10↑", Delay::between(neg_strict, pos_weak).to_string());

        assert_eq!("10", Delay::between(neg_weak, pos_weak).to_string());
        assert_eq!("10↓", Delay::between(neg_weak, pos_strict).to_string());
    }
}
