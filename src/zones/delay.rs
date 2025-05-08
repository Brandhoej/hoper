use std::{cmp::Ordering, fmt, ops::Add};

use super::constraint::{Limit, Relation, Strictness, INFINITY};

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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

    /// Represents an unbounded delay in the positive direction.
    Up,
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

    /// Constructs an unbounded positive delay.
    pub const fn up() -> Self {
        Self::Up
    }

    /// Constructs a delay that represents the delay between `before` and `after`.
    pub const fn between(before: Relation, after: Relation) -> Result<Self, ()> {
        match (before.is_infinity(), after.is_infinity()) {
            (false, true) => return Ok(Self::up()),
            (true, true) => return Ok(Self::exact(0)),
            (true, false) => return Err(()),
            (_, _) => {}
        }

        let limit = after.limit() - before.limit();
        let delay = match (before.strictness(), after.strictness()) {
            (Strictness::Strict, Strictness::Strict) | (Strictness::Weak, Strictness::Weak) => {
                Self::exact(limit)
            }
            (Strictness::Strict, Strictness::Weak) => Self::relax(limit),
            (Strictness::Weak, Strictness::Strict) => Self::tighten(limit),
        };

        Ok(delay)
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

    /// Returns `true` if the delay is infinite.
    pub const fn is_up(&self) -> bool {
        matches!(self, Delay::Up)
    }

    /// Returns the numerical component of the delay.
    pub const fn limit(&self) -> Option<Limit> {
        match self {
            Delay::Exact(limit) | Delay::Relaxed(limit) | Delay::Tightened(limit) => Some(*limit),
            Delay::Up => None,
        }
    }

    /// Applies this delay to a clock constraint, producing a new relation.
    ///
    /// This is typically used to compute the effect of time progression on
    /// upper bounds in DBMs. The delay adjusts the limit and may alter the
    /// strictness depending on its variant (`Relaxed`, `Tightened`, or `Exact`).
    pub fn elapse(&self, relation: Relation) -> Relation {
        match self {
            Delay::Up => INFINITY,
            Delay::Exact(d) | Delay::Relaxed(d) | Delay::Tightened(d) => {
                if relation.is_infinity() {
                    return relation;
                }

                let limit = *d + relation.limit();
                let strictness = match self {
                    Delay::Exact(_) => relation.strictness(),
                    Delay::Relaxed(_) => Strictness::Weak,
                    Delay::Tightened(_) => Strictness::Strict,
                    _ => unreachable!(), // Redundant now, but retained defensively
                };
                Relation::new(limit, strictness)
            }
        }
    }
}

impl fmt::Display for Delay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Delay::Exact(limit) => write!(f, "{}", limit),
            Delay::Relaxed(limit) => write!(f, "{}↑", limit),
            Delay::Tightened(limit) => write!(f, "{}↓", limit),
            Delay::Up => write!(f, "∞↑"),
        }
    }
}

impl Ord for Delay {
    fn cmp(&self, other: &Self) -> Ordering {
        if !self.is_up() && !other.is_up() {
            let limit = self.limit().cmp(&other.limit());
            if limit != Ordering::Equal {
                return limit;
            }
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

            (Delay::Up, Delay::Up) => Ordering::Equal,
            (Delay::Up, Delay::Relaxed(_)) => Ordering::Greater,
            (Delay::Up, Delay::Tightened(_)) => Ordering::Greater,
            (Delay::Up, Delay::Exact(_)) => Ordering::Greater,
            (Delay::Relaxed(_), Delay::Up) => Ordering::Less,
            (Delay::Tightened(_), Delay::Up) => Ordering::Less,
            (Delay::Exact(_), Delay::Up) => Ordering::Less,
        }
    }
}

impl PartialOrd for Delay {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Add<Relation> for Delay {
    type Output = Relation;

    fn add(self, rhs: Relation) -> Self::Output {
        self.elapse(rhs)
    }
}

impl Add<Delay> for Relation {
    type Output = Relation;

    fn add(self, rhs: Delay) -> Self::Output {
        rhs + self
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use crate::zones::{
        constraint::{Relation, INFINITY},
        delay::Delay,
    };

    #[test]
    fn delay_limit() {
        assert_eq!(Some(123), Delay::exact(123).limit());
        assert_eq!(Some(123), Delay::relax(123).limit());
        assert_eq!(Some(123), Delay::tighten(123).limit());
        assert_eq!(Some(-123), Delay::exact(-123).limit());
        assert_eq!(Some(-123), Delay::relax(-123).limit());
        assert_eq!(Some(-123), Delay::tighten(-123).limit());
        assert_eq!(None, Delay::up().limit())
    }

    #[test]
    fn delay_type() {
        assert!(Delay::exact(1).is_exact());
        assert!(!Delay::exact(1).is_relaxed());
        assert!(!Delay::exact(1).is_tightened());
        assert!(!Delay::exact(1).is_up());
        assert!(Delay::relax(1).is_relaxed());
        assert!(!Delay::relax(1).is_exact());
        assert!(!Delay::relax(1).is_tightened());
        assert!(!Delay::relax(1).is_up());
        assert!(Delay::tighten(1).is_tightened());
        assert!(!Delay::tighten(1).is_exact());
        assert!(!Delay::tighten(1).is_relaxed());
        assert!(!Delay::tighten(1).is_up());
        assert!(Delay::up().is_up());
        assert!(!Delay::up().is_tightened());
        assert!(!Delay::up().is_exact());
        assert!(!Delay::up().is_relaxed());
    }

    #[test]
    fn elapse() {
        assert_eq!("(2, ≤)", (Delay::relax(1) + Relation::weak(1)).to_string());
        assert_eq!(
            "(2, ≤)",
            (Delay::relax(1) + Relation::strict(1)).to_string()
        );
        assert_eq!(
            "(2, <)",
            (Delay::tighten(1) + Relation::weak(1)).to_string()
        );
        assert_eq!(
            "(2, <)",
            (Delay::tighten(1) + Relation::strict(1)).to_string()
        );
        assert_eq!("(2, ≤)", (Delay::exact(1) + Relation::weak(1)).to_string());
        assert_eq!(
            "(2, <)",
            (Delay::exact(1) + Relation::strict(1)).to_string()
        );

        assert_eq!("(0, ≤)", (Delay::relax(-1) + Relation::weak(1)).to_string());
        assert_eq!(
            "(0, ≤)",
            (Delay::relax(-1) + Relation::strict(1)).to_string()
        );
        assert_eq!(
            "(0, <)",
            (Delay::tighten(-1) + Relation::weak(1)).to_string()
        );
        assert_eq!(
            "(0, <)",
            (Delay::tighten(-1) + Relation::strict(1)).to_string()
        );
        assert_eq!("(0, ≤)", (Delay::exact(-1) + Relation::weak(1)).to_string());
        assert_eq!(
            "(0, <)",
            (Delay::exact(-1) + Relation::strict(1)).to_string()
        );
    }

    #[test]
    fn between() {
        assert_eq!(
            "1",
            Delay::between(Relation::weak(1), Relation::weak(2))
                .unwrap()
                .to_string()
        );
        assert_eq!(
            "1",
            Delay::between(Relation::strict(1), Relation::strict(2))
                .unwrap()
                .to_string()
        );
        assert_eq!(
            "1↑",
            Delay::between(Relation::strict(1), Relation::weak(2))
                .unwrap()
                .to_string()
        );
        assert_eq!(
            "1↓",
            Delay::between(Relation::weak(1), Relation::strict(2))
                .unwrap()
                .to_string()
        );
        assert_eq!(
            "∞↑",
            Delay::between(Relation::weak(1), INFINITY)
                .unwrap()
                .to_string()
        );
        // between INF and INF is defined based on their subtraction.
        assert_eq!("(0, ≤)", (INFINITY - INFINITY).to_string());
        assert_eq!("0", Delay::between(INFINITY, INFINITY).unwrap().to_string());
    }

    #[test]
    fn delay_order() {
        let exact = Delay::exact(5);
        let relaxed = Delay::relax(5);
        let tightened = Delay::tighten(5);
        let up = Delay::up();

        assert_eq!(Ordering::Equal, relaxed.cmp(&relaxed));
        assert_eq!(Ordering::Greater, relaxed.cmp(&exact));
        assert_eq!(Ordering::Greater, relaxed.cmp(&tightened));
        assert_eq!(Ordering::Less, relaxed.cmp(&up));
        assert_eq!(Ordering::Equal, tightened.cmp(&tightened));
        assert_eq!(Ordering::Less, tightened.cmp(&exact));
        assert_eq!(Ordering::Less, tightened.cmp(&relaxed));
        assert_eq!(Ordering::Less, tightened.cmp(&up));
        assert_eq!(Ordering::Equal, exact.cmp(&exact));
        assert_eq!(Ordering::Less, exact.cmp(&relaxed));
        assert_eq!(Ordering::Greater, exact.cmp(&tightened));
        assert_eq!(Ordering::Less, exact.cmp(&up));
        assert_eq!(Ordering::Equal, up.cmp(&up));
        assert_eq!(Ordering::Greater, up.cmp(&exact));
        assert_eq!(Ordering::Greater, up.cmp(&relaxed));
        assert_eq!(Ordering::Greater, up.cmp(&tightened));
    }

    #[test]
    fn delay_between() {
        let neg_strict = Relation::strict(-5);
        let neg_weak = Relation::weak(-5);
        let pos_strict = Relation::strict(5);
        let pos_weak = Relation::weak(5);

        assert_eq!(
            "0",
            Delay::between(neg_strict, neg_strict).unwrap().to_string()
        );
        assert_eq!("0", Delay::between(neg_weak, neg_weak).unwrap().to_string());
        assert_eq!(
            "0",
            Delay::between(pos_strict, pos_strict).unwrap().to_string()
        );
        assert_eq!("0", Delay::between(pos_weak, pos_weak).unwrap().to_string());

        assert_eq!(
            "10",
            Delay::between(neg_strict, pos_strict).unwrap().to_string()
        );
        assert_eq!(
            "10↑",
            Delay::between(neg_strict, pos_weak).unwrap().to_string()
        );

        assert_eq!(
            "10",
            Delay::between(neg_weak, pos_weak).unwrap().to_string()
        );
        assert_eq!(
            "10↓",
            Delay::between(neg_weak, pos_strict).unwrap().to_string()
        );
    }
}
