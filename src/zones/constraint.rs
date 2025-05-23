use std::{
    cmp::Ordering,
    fmt,
    ops::{Add, AddAssign, Neg, Sub, SubAssign},
    u16, usize,
};

use rand::{
    distributions::{
        uniform::{SampleBorrow, SampleUniform, UniformSampler},
        Standard, Uniform,
    },
    prelude::Distribution,
    Rng,
};

use super::delay::Delay;

/// The unique index of a clock. This can be used to directly address the DBM.
pub type Clock = u16;

/// The zero'th (0) clock is the reference clock and marker of inconsistency.
pub const REFERENCE: Clock = 0;

/// Describes the strictness (<, <=) of the constraint between two clocks in the DBM.
#[derive(PartialEq, Debug, Clone, Copy, Eq, Ord)]
pub enum Strictness {
    /// <
    Strict,
    /// <=
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

impl From<Strictness> for u8 {
    fn from(value: Strictness) -> Self {
        match value {
            Strictness::Strict => 0,
            Strictness::Weak => 1,
        }
    }
}

impl Distribution<Strictness> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Strictness {
        match rng.gen_range(Strictness::Strict.into()..=Strictness::Weak.into()) {
            0 => Strictness::Strict,
            _ => Strictness::Weak,
        }
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

impl PartialOrd for Strictness {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self {
            Strictness::Strict => match other {
                Strictness::Strict => Some(Ordering::Equal),
                Strictness::Weak => Some(Ordering::Less),
            },
            Strictness::Weak => match other {
                Strictness::Strict => Some(Ordering::Greater),
                Strictness::Weak => Some(Ordering::Equal),
            },
        }
    }
}

pub struct UniformStrictness {
    low: Strictness,
    high: Strictness,
    inclusive: bool,
}

impl UniformSampler for UniformStrictness {
    type X = Strictness;

    fn new<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = low.borrow();
        let high = high.borrow();

        if low >= high {
            panic!("low cannot be higher than high")
        }

        Self {
            low: *low,
            high: *high,
            inclusive: false,
        }
    }

    fn new_inclusive<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = low.borrow();
        let high = high.borrow();

        if low > high {
            panic!("low cannot be higher than high")
        }

        Self {
            low: *low,
            high: *high,
            inclusive: true,
        }
    }

    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        let value = if self.inclusive {
            rng.gen_range(self.low.into()..=self.high.into())
        } else {
            rng.gen_range(self.low.into()..self.high.into())
        };

        match value {
            0 => Strictness::Strict,
            _ => Strictness::Weak,
        }
    }
}

impl SampleUniform for Strictness {
    type Sampler = UniformStrictness;
}

pub type Limit = i16;

/// An element optimized for caching which represents a strict or weak
/// relation between two clocks (c0 - c1 RELATION). This encoding uses
/// the least significant bit to represent the strictness and the other
/// bits as the limit. The encoding is [limit] [1 bit strictness].
#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub struct Relation(Limit);

/// The minimum possible limit the relation supports is an i15 minimum equivalent.
pub const MIN_LIMIT: Limit = -16384;
/// The maximum possible limit the relation supports is an i15 maximum equivalent.
pub const MAX_LIMIT: Limit = 16383;

/// Inifity is all 1's (Max unsigned bit representation) this is the same as (∞, ≤).
pub const INFINITY: Relation = Relation::new(MAX_LIMIT, Strictness::Weak);
/// Zero is just a relation with limit of 0 but it is weak and thereby includes 0 (0, ≤).
///
/// TODO: More appropriately this should be called `POSITIVE`.
pub const ZERO: Relation = Relation::new(0, Strictness::Weak);
/// Describes the relation consisting of all negative number (0, <).
pub const NEGATIVE: Relation = Relation::new(0, Strictness::Strict);

impl Relation {
    pub const fn new(limit: Limit, strictness: Strictness) -> Self {
        let strictness_bit = match strictness {
            Strictness::Strict => 0,
            Strictness::Weak => 1,
        };
        Self((limit << 1) | strictness_bit)
    }

    pub const fn weak(limit: Limit) -> Self {
        Self::new(limit, Strictness::Weak)
    }

    pub const fn strict(limit: Limit) -> Self {
        Self::new(limit, Strictness::Strict)
    }

    pub fn clamp(self, min: Self, max: Self) -> Self {
        if max < min {
            panic!("max is less than min");
        }

        if self < min {
            return min;
        } else if self > max {
            return max;
        } else {
            return self;
        }
    }

    /// Returns the limit of the relation which can be
    /// represented with one less bit than the relation
    /// as the last bit describes the relation's strictness.
    pub const fn limit(&self) -> Limit {
        if self.is_infinity() {
            panic!("no limit when infinity")
        }
        self.0 >> 1
    }

    pub fn equal_limit(&self, other: &Self) -> bool {
        if self.is_infinity() && other.is_infinity() {
            true
        } else if self.is_infinity() && !other.is_infinity() {
            false
        } else if !self.is_infinity() && other.is_infinity() {
            false
        } else {
            self.limit() == other.limit()
        }
    }

    pub fn greater_limit(&self, other: &Self) -> bool {
        if self.is_infinity() && other.is_infinity() {
            false
        } else if self.is_infinity() && !other.is_infinity() {
            false
        } else if !self.is_infinity() && other.is_infinity() {
            false
        } else {
            self.limit() > other.limit()
        }
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
        if self.equals(&ZERO) {
            return ZERO;
        }
        if self.equals(&INFINITY) {
            return INFINITY;
        }
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
    ///
    /// OBS: Addition can overflow!
    pub const fn addition(&self, other: &Self) -> Self {
        if other.is_zero() {
            return *self;
        }

        if self.is_zero() {
            return *other;
        }

        if self.is_infinity() || other.is_infinity() {
            return INFINITY;
        }

        // First adding the lhs and rhs increases the limit.
        // Then we ensure the tightest constraint that satisfies both constraints is kept.
        Self((self.0 + other.0) - ((self.0 | other.0) & 1))
    }

    pub const fn equals(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    /// subtract other from self by "self + (-other)".
    pub const fn subtraction(&self, other: &Self) -> Self {
        if self.equals(other) {
            return ZERO;
        }
        self.addition(&other.negation())
    }

    pub const fn extend(self, limit: Limit) -> Self {
        Self::new(self.limit() + limit, self.strictness())
    }

    pub const fn shrink(self, limit: Limit) -> Self {
        Self::new(self.limit() - limit, self.strictness())
    }

    pub fn abs(self) -> Self {
        if self.is_infinity() {
            return self;
        }

        if self.limit() < 0 {
            Self::new(-self.limit(), self.strictness())
        } else {
            self
        }
    }

    pub fn difference(self, other: Self) -> Self {
        if self > other {
            self - other
        } else {
            other - self
        }
    }

    pub fn length(self) -> Self {
        Self::new(self.limit().abs(), Strictness::Weak)
    }

    pub fn negate_limit(self) -> Self {
        Self::new(-self.limit(), self.strictness())
    }
}

impl Ord for Relation {
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

impl Neg for Relation {
    type Output = Relation;

    fn neg(self) -> Self::Output {
        self.negation()
    }
}

impl Add for Relation {
    type Output = Relation;

    fn add(self, rhs: Self) -> Self::Output {
        self.addition(&rhs)
    }
}

impl AddAssign for Relation {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs
    }
}

impl Sub for Relation {
    type Output = Relation;

    fn sub(self, rhs: Self) -> Self::Output {
        self.subtraction(&rhs)
    }
}

impl SubAssign for Relation {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs
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

impl Distribution<Relation> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Relation {
        let strictness: Strictness = rng.gen();
        let limit: Limit = rng.gen_range(MIN_LIMIT..=MAX_LIMIT);
        Relation::new(limit, strictness)
    }
}

pub struct UniformRelation {
    low: Relation,
    high: Relation,
    inclusive: bool,
}

impl UniformSampler for UniformRelation {
    type X = Relation;

    fn new<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = low.borrow();
        let high = high.borrow();

        if low >= high {
            panic!("low cannot be higher than high");
        }

        Self {
            low: *low,
            high: *high,
            inclusive: false,
        }
    }

    fn new_inclusive<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = low.borrow();
        let high = high.borrow();

        if low > high {
            panic!("low cannot be higher than high");
        }

        Self {
            low: *low,
            high: *high,
            inclusive: true,
        }
    }

    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        // FIXME: Cannot generate INFINITY as the limit is accessed which is not supported for infinity.
        let limit = if self.inclusive {
            rng.gen_range(self.low.limit()..=self.high.limit())
        } else {
            rng.gen_range(self.low.limit()..self.high.limit())
        };

        let (strictest, weakest) = if self.low.limit() == self.high.limit() {
            (self.low.strictness(), self.high.strictness())
        } else if limit == self.low.limit() {
            (self.low.strictness(), Strictness::Weak)
        } else if limit == self.high.limit() {
            (Strictness::Strict, self.high.strictness())
        } else {
            (Strictness::Strict, Strictness::Weak)
        };
        let strictness: Strictness = Uniform::new_inclusive(strictest, weakest).sample(rng);

        Relation::new(limit, strictness)
    }
}

impl SampleUniform for Relation {
    type Sampler = UniformRelation;
}

#[derive(Clone)]
pub struct RelationsSample(Vec<Relation>);

impl RelationsSample {
    pub fn new(relations: Vec<Relation>) -> Self {
        Self(relations)
    }

    pub fn relations(self) -> Vec<Relation> {
        self.0
    }
}

impl From<Box<[Relation]>> for RelationsSample {
    fn from(value: Box<[Relation]>) -> Self {
        Self::new(value.into_vec())
    }
}

impl From<RelationsSample> for Box<[Relation]> {
    fn from(value: RelationsSample) -> Self {
        value.0.into_boxed_slice()
    }
}

pub struct UniformRelations {
    low: RelationsSample,
    high: RelationsSample,
    n: usize,
    inclusive: bool,
}

impl UniformSampler for UniformRelations {
    type X = RelationsSample;

    fn new<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = low.borrow();
        let high = high.borrow();

        let n = low.0.len();
        if high.0.len() != n {
            panic!("low and high must have the same lengths")
        }

        for i in 0..n {
            if low.0[i] >= high.0[i] {
                panic!("low cannot be higher than high");
            }
        }

        Self {
            low: low.clone(),
            high: high.clone(),
            n,
            inclusive: false,
        }
    }

    fn new_inclusive<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = low.borrow();
        let high = high.borrow();

        let n = low.0.len();
        if high.0.len() != n {
            panic!("low and high must have the same lengths")
        }

        for i in 0..n {
            if low.0[i] > high.0[i] {
                panic!("low cannot be higher than high");
            }
        }

        Self {
            low: low.clone(),
            high: high.clone(),
            n,
            inclusive: true,
        }
    }

    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        let mut sample = Vec::with_capacity(self.n);
        for i in 0..self.n {
            let low = self.low.0[i];
            let high = self.high.0[i];

            let sampler = if self.inclusive {
                Uniform::new_inclusive(low, high)
            } else {
                Uniform::new(low, high)
            };

            sample.push(sampler.sample(rng));
        }
        RelationsSample(sample)
    }
}

impl SampleUniform for RelationsSample {
    type Sampler = UniformRelations;
}

impl fmt::Display for Relation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_infinity() {
            return write!(f, "(∞, {})", self.strictness());
        }
        write!(f, "({}, {})", self.limit(), self.strictness())
    }
}

#[derive(Clone)]
pub struct Constraint {
    minuend: Clock,
    subtrahend: Clock,
    relation: Relation,
}

impl Constraint {
    pub const fn new(minuend: Clock, subtrahend: Clock, relation: Relation) -> Self {
        Self {
            minuend,
            subtrahend,
            relation,
        }
    }

    pub const fn upper(clock: Clock, relation: Relation) -> Self {
        Self::new(clock, REFERENCE, relation)
    }

    pub const fn lower(clock: Clock, relation: Relation) -> Self {
        Self::new(REFERENCE, clock, relation)
    }

    pub const fn indefinite(clock: Clock) -> Self {
        Self::upper(clock, INFINITY)
    }

    pub fn minuend(&self) -> Clock {
        self.minuend.clone()
    }

    pub fn subtrahend(&self) -> Clock {
        self.subtrahend.clone()
    }

    pub fn relation(&self) -> Relation {
        self.relation.clone()
    }
}

impl fmt::Display for Constraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} - {} {}",
            self.minuend, self.subtrahend, self.relation
        )
    }
}

#[cfg(test)]
mod tests {
    use rand::{distributions::Uniform, Rng};

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
        assert_eq!(
            MIN_LIMIT,
            Relation::new(MIN_LIMIT, Strictness::Weak).limit()
        );

        let mut rng = rand::thread_rng();
        for _ in 0..10_000 {
            let limit = rng.gen_range(MIN_LIMIT..=MAX_LIMIT - 1);
            let relation = Relation::new(limit, Strictness::Weak);
            assert_eq!(limit, relation.limit())
        }
    }

    #[test]
    fn inifinity() {
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
        );
        assert_eq!("(0, ≤)", ZERO.negation().to_string());
        assert_eq!("(∞, ≤)", INFINITY.negation().to_string());
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

    #[test]
    fn relation_distribution_bounds() {
        let mut rng = rand::thread_rng();
        for _ in 0..=MAX_LIMIT {
            let relation: Relation = rng.gen();
            assert!(
                relation >= Relation::new(MIN_LIMIT, Strictness::Strict)
                    && relation <= Relation::new(MAX_LIMIT, Strictness::Weak)
            );
        }
    }

    #[test]
    fn strictness_uniform_sampler() {
        let mut rng = rand::thread_rng();
        let low = Strictness::Strict;
        let high = Strictness::Weak;
        let sampler = Uniform::new(low, high);
        for _ in 0..=100 {
            let strictness = sampler.sample(&mut rng);
            assert!(strictness >= low && strictness < high);
        }
    }

    #[test]
    fn strictness_uniform_inclusive_sampler() {
        let mut rng = rand::thread_rng();
        let low = Strictness::Weak;
        let high = Strictness::Weak;
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..=100 {
            let strictness = sampler.sample(&mut rng);
            assert!(strictness >= low && strictness <= high);
        }
    }

    #[test]
    fn relation_uniform_sampler() {
        let mut rng = rand::thread_rng();
        let low = Relation::new(100, Strictness::Strict);
        let high = Relation::new(1000, Strictness::Strict);
        let sampler = Uniform::new(low, high);
        for _ in 0..=MAX_LIMIT as usize * 100 {
            let relation = sampler.sample(&mut rng);
            assert!(relation >= low && relation < high);
        }
    }

    #[test]
    fn relation_uniform_inclusive_sampler() {
        let mut rng = rand::thread_rng();
        let low = Relation::new(100, Strictness::Strict);
        let high = Relation::new(1000, Strictness::Strict);
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..=MAX_LIMIT as usize * 100 {
            let relation = sampler.sample(&mut rng);
            assert!(relation >= low && relation <= high);
        }
    }

    #[test]
    fn relation_uniform_never_less_than_zero() {
        let mut rng = rand::thread_rng();
        let low = ZERO;
        let high = Relation::new(15, Strictness::Strict);
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..=MAX_LIMIT as usize * 100 {
            let relation = sampler.sample(&mut rng);
            assert!(relation >= ZERO)
        }
    }

    #[test]
    fn relation_uniform_less_than_zero() {
        let mut rng = rand::thread_rng();
        let low = Relation::new(0, Strictness::Strict);
        let high = Relation::new(0, Strictness::Strict);
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..=MAX_LIMIT as usize * 100 {
            let relation = sampler.sample(&mut rng);
            assert!(relation == Relation::new(0, Strictness::Strict))
        }
    }

    #[test]
    fn addition_commutative_property() {
        let mut rng = rand::thread_rng();
        let low = ZERO;
        let high = Relation::new(50, Strictness::Strict);
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..1000 {
            let a = sampler.sample(&mut rng);
            let b = sampler.sample(&mut rng);
            assert_eq!(a + b, b + a);
        }
    }

    #[test]
    fn addition_cancels_subtraction() {
        let mut rng = rand::thread_rng();
        let low = ZERO;
        let high = Relation::new(50, Strictness::Strict);
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..1000 {
            let a = sampler.sample(&mut rng);
            let b = sampler.sample(&mut rng);
            assert_eq!(a, a + (b - b));
            assert_eq!(b, b + (a - a));
            if a != ZERO && a.strictness() > b.strictness() {
                assert_ne!(a, b + a - b);
            }
            if b != ZERO && b.strictness() > a.strictness() {
                assert_ne!(b, a + b - a);
            }
        }
    }

    #[test]
    fn addition_associative_property() {
        let mut rng = rand::thread_rng();
        let low = ZERO;
        let high = Relation::new(50, Strictness::Strict);
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..1000 {
            let a = sampler.sample(&mut rng);
            let b = sampler.sample(&mut rng);
            let c = sampler.sample(&mut rng);
            assert_eq!(a + (b + c), (a + b) + c);
        }
    }

    #[test]
    fn addition_identity_property() {
        let mut rng = rand::thread_rng();
        let low = ZERO;
        let high = Relation::new(50, Strictness::Strict);
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..1000 {
            let a = sampler.sample(&mut rng);
            assert_eq!(a + ZERO, a);
        }
    }

    #[test]
    fn relation_uniform_zero() {
        let mut rng = rand::thread_rng();
        let low = ZERO;
        let high = ZERO;
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..=MAX_LIMIT as usize * 100 {
            let relation = sampler.sample(&mut rng);
            assert!(relation == ZERO)
        }
    }

    #[test]
    fn subtraction_non_commutativity() {
        let mut rng = rand::thread_rng();
        let low = ZERO;
        let high = Relation::new(50, Strictness::Strict);
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..1000 {
            let a = sampler.sample(&mut rng);
            let b = sampler.sample(&mut rng);
            if a != b {
                assert_ne!(a - b, b - a);
            } else {
                assert_eq!(ZERO, a - b);
                assert_eq!(ZERO, b - a);
            }
        }
    }

    #[test]
    fn subtraction_with_identity() {
        let mut rng = rand::thread_rng();
        let low = ZERO;
        let high = Relation::new(50, Strictness::Strict);
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..1000 {
            let a = sampler.sample(&mut rng);
            assert_eq!(-a, ZERO - a, "{} =? {} = {} - {}", -a, ZERO - a, ZERO, a);
            assert_eq!(a, a - ZERO, "{} =? {} = {} - {}", a, a - ZERO, a, ZERO);
        }
    }

    #[test]
    fn inversion_and_identities() {
        let mut rng = rand::thread_rng();
        let low = ZERO;
        let high = Relation::new(50, Strictness::Strict);
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..1000 {
            let a = sampler.sample(&mut rng);
            assert_eq!(ZERO, a - a);
            assert_eq!(a, a - ZERO);
            assert_eq!(a, a + ZERO);
        }
    }

    #[test]
    fn subtraction_non_associativity() {
        let mut rng = rand::thread_rng();
        let low = ZERO;
        let high = Relation::new(50, Strictness::Strict);
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..1000 {
            let a = sampler.sample(&mut rng);
            let b = sampler.sample(&mut rng);
            let c = sampler.sample(&mut rng);
            if c != ZERO {
                assert_ne!(a - (b - c), (a - b) - c, "{}, {}, {}", a, b, c);
            }
        }
    }

    #[test]
    fn relations() {
        assert!(INFINITY == INFINITY);
        assert!(INFINITY >= INFINITY);
        assert!(INFINITY <= INFINITY);
        assert!(!(INFINITY > INFINITY));
        assert!(!(INFINITY < INFINITY));
        assert!(ZERO == ZERO);
        assert!(ZERO >= ZERO);
        assert!(ZERO <= ZERO);
        assert!(!(ZERO > ZERO));
        assert!(!(ZERO < ZERO));
        assert!(ZERO < INFINITY);
        assert!(ZERO <= INFINITY);
        assert!(Relation::weak(1) == Relation::weak(1));
        assert!(Relation::strict(1) == Relation::strict(1));
        assert!(Relation::weak(1) > Relation::strict(1));
        assert!(Relation::weak(10) > Relation::strict(1));
        assert!(Relation::strict(1) < Relation::weak(1));
        assert!(Relation::strict(10) > Relation::weak(1));
    }

    /*#[test] FIXME: Infinity is not supported
    fn relation_uniform_infinity() {
        let mut rng = rand::thread_rng();
        let low = INFINITY;
        let high = INFINITY;
        let sampler = Uniform::new_inclusive(low, high);
        for _ in 0..=MAX_LIMIT as usize * 100 {
            let relation = sampler.sample(&mut rng);
            assert!(relation == INFINITY)
        }
    }*/

    #[test]
    fn addition() {
        assert_eq!(ZERO.addition(&ZERO), ZERO);
        assert_eq!(ZERO.addition(&INFINITY), INFINITY);
        assert_eq!(INFINITY.addition(&INFINITY), INFINITY);
        assert_eq!(
            Relation::weak(10).addition(&Relation::weak(10)),
            Relation::weak(20)
        );
        assert_eq!(
            Relation::weak(10).addition(&Relation::strict(10)),
            Relation::strict(20)
        );
        assert_eq!(
            Relation::strict(10).addition(&Relation::weak(10)),
            Relation::strict(20)
        );
        assert_eq!(
            Relation::strict(10).addition(&Relation::strict(10)),
            Relation::strict(20)
        );
    }

    #[test]
    fn abs() {
        assert_eq!("(0, ≤)", ZERO.abs().to_string());
        assert_eq!("(0, <)", NEGATIVE.abs().to_string());
        assert_eq!("(10, ≤)", Relation::weak(10).abs().to_string());
        assert_eq!("(10, ≤)", Relation::weak(-10).abs().to_string());
        assert_eq!("(10, <)", Relation::strict(10).abs().to_string());
        assert_eq!("(10, <)", Relation::strict(-10).abs().to_string());
    }

    #[test]
    fn difference() {
        assert_eq!("(2, <)", ZERO.difference(Relation::strict(2)).to_string());
        assert_eq!("(2, ≤)", ZERO.difference(Relation::weak(2)).to_string());
    }
}
