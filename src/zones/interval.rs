use std::fmt::Display;

use super::{
    constraint::{Limit, Relation},
    delay::Delay,
};

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub struct Interval {
    lower: Relation,
    upper: Relation,
}

impl Interval {
    pub fn new(lower: Relation, upper: Relation) -> Self {
        if lower > upper {
            panic!();
        }
        Self { lower, upper }
    }

    pub fn closed(lower: Limit, upper: Limit) -> Self {
        Self::new(Relation::weak(lower), Relation::weak(upper))
    }

    pub fn opened(lower: Limit, upper: Limit) -> Self {
        Self::new(Relation::strict(lower), Relation::strict(upper))
    }

    pub fn singleton(limit: Limit) -> Self {
        Self::closed(limit, limit)
    }

    pub const fn lower(&self) -> Relation {
        self.lower
    }

    pub const fn upper(&self) -> Relation {
        self.upper
    }

    pub fn delay(&self) -> Delay {
        Delay::between(self.lower, self.upper).ok().unwrap()
    }

    pub fn between(&self, other: &Self) -> Option<Delay> {
        if self.upper < other.lower {
            Some(Delay::between(self.upper, other.lower).ok().unwrap())
        } else if other.upper < self.lower {
            Some(Delay::between(other.upper, self.lower).ok().unwrap())
        } else {
            None
        }
    }

    pub fn intersection(&self, other: &Self) -> Option<Self> {
        let lower_limit = self.lower.max(other.lower);
        let upper_limit = self.upper.min(other.upper);

        let lower_strictness = if self.lower.equal_limit(&other.lower()) {
            self.lower.strictness().min(other.lower.strictness())
        } else {
            if self.lower.greater_limit(&other.lower) {
                self.lower.strictness()
            } else {
                other.lower.strictness()
            }
        };

        let upper_strictness = if self.upper.equal_limit(&other.upper()) {
            self.upper.strictness().min(other.upper.strictness())
        } else {
            if self.upper.greater_limit(&other.upper) {
                other.upper.strictness()
            } else {
                self.upper.strictness()
            }
        };

        let lower_relation = if lower_limit.is_infinity() {
            lower_limit
        } else {
            Relation::new(lower_limit.limit(), lower_strictness)
        };
        let upper_relation = if upper_limit.is_infinity() {
            upper_limit
        } else {
            Relation::new(upper_limit.limit(), upper_strictness)
        };

        if lower_relation > upper_relation
            || upper_relation < lower_relation
            || (lower_relation.equal_limit(&upper_relation)
                && (lower_relation.is_strict() || upper_relation.is_strict()))
        {
            return None;
        }

        Some(Self::new(lower_relation, upper_relation))
    }
}

impl Display for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let lower_bracket = if self.lower.is_weak() { "[" } else { "(" };
        let upper_bracket = if self.upper.is_weak() { "]" } else { ")" };

        let lower_limit = if self.lower.is_infinity() {
            "∞".to_string()
        } else {
            self.lower.limit().to_string()
        };

        let upper_limit = if self.upper.is_infinity() {
            "∞".to_string()
        } else {
            self.upper.limit().to_string()
        };

        write!(
            f,
            "{}{}, {}{}",
            lower_bracket, lower_limit, upper_limit, upper_bracket
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::zones::{constraint::Relation, interval::Interval};

    #[test]
    fn included() {
        assert_eq!("10", Interval::closed(12, 22).delay().to_string());
        assert_eq!("0", Interval::closed(12, 12).delay().to_string());
        assert_eq!("10", Interval::closed(-22, -12).delay().to_string());
        assert_eq!("0", Interval::closed(-12, -12).delay().to_string());
        assert_eq!("34", Interval::closed(-22, 12).delay().to_string());
        assert_eq!("24", Interval::closed(-12, 12).delay().to_string());

        assert_eq!("1", Interval::opened(0, 1).delay().to_string());
        assert_eq!("2", Interval::opened(3, 5).delay().to_string());

        assert_eq!(
            "1↑",
            Interval::new(Relation::strict(3), Relation::weak(4))
                .delay()
                .to_string()
        );
    }

    #[test]
    fn intersects() {
        assert!(Interval::closed(10, 13)
            .intersection(&Interval::closed(11, 15))
            .is_some());
        assert!(Interval::closed(10, 13)
            .intersection(&Interval::closed(14, 15))
            .is_none());
        assert!(Interval::closed(10, 13)
            .intersection(&Interval::opened(13, 15))
            .is_none());
        assert!(Interval::closed(10, 13)
            .intersection(&Interval::opened(5, 10))
            .is_none());
    }

    #[test]
    fn between() {
        assert!(Interval::closed(0, 0)
            .between(&Interval::closed(0, 0))
            .is_none());
        assert!(Interval::closed(0, 10)
            .between(&Interval::closed(5, 5))
            .is_none());
        assert!(Interval::opened(0, 1)
            .between(&Interval::opened(0, 1))
            .is_none());
        assert!(Interval::opened(0, 10)
            .between(&Interval::opened(5, 5))
            .is_none());

        assert_eq!(
            "1",
            Interval::closed(0, 0)
                .between(&Interval::closed(1, 1))
                .unwrap()
                .to_string()
        );
        assert_eq!(
            "1↓",
            Interval::closed(0, 0)
                .between(&Interval::opened(1, 2))
                .unwrap()
                .to_string()
        );
        assert_eq!(
            "1↓",
            Interval::opened(1, 2)
                .between(&Interval::closed(0, 0))
                .unwrap()
                .to_string()
        );
        assert_eq!(
            "1",
            Interval::opened(1, 2)
                .between(&Interval::opened(3, 4))
                .unwrap()
                .to_string()
        );
    }

    #[test]
    fn intersection() {
        assert_eq!(
            "[11, 12]",
            Interval::closed(10, 15)
                .intersection(&Interval::closed(11, 12))
                .unwrap()
                .to_string()
        );
        assert_eq!(
            "[11, 15]",
            Interval::closed(10, 15)
                .intersection(&Interval::closed(11, 17))
                .unwrap()
                .to_string()
        );
        assert_eq!(
            "[11, 15)",
            Interval::opened(10, 15)
                .intersection(&Interval::closed(11, 17))
                .unwrap()
                .to_string()
        );
        assert_eq!(
            "(1, 2)",
            Interval::opened(1, 2)
                .intersection(&Interval::closed(1, 2))
                .unwrap()
                .to_string()
        );
    }
}
