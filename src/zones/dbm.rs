use core::panic;
use std::ops::{Index, IndexMut};

use bitset::BitSet;
use rand::{distributions::{uniform::{SampleBorrow, UniformSampler}, Standard}, prelude::Distribution, Rng};

use super::constraint::{Clock, Limit, Relation, Strictness, INFINITY, REFERENCE, ZERO};

pub trait DBMState: Sized {}

#[derive(Clone)]
pub struct DBM<State: DBMState> {
    /// The number of clocks inside the DBM.
    clocks: Clock,
    /// The relations across the clocks.
    relations: Vec<Relation>,
    /// The internal state important for the current type of DBM.
    state: State,
}

impl<State: DBMState> DBM<State> {
    pub const fn clocks(&self) -> Clock {
        self.clocks
    }

    pub const fn constraints(&self) -> usize {
        (self.clocks() * self.clocks()) as usize
    }

    /// Uses the row-wise indexing and not the layered approach since we have the clock set in the DBM.
    ///
    /// Eg. 3 clocks (including the reference clock) DBM indexing "(row; column)-index":
    ///
    /// [(0; 0)-0, (0; 1)-1, (0; 2)-2]
    ///
    /// [(1; 0)-3, (1; 1)-4, (1; 2)-5]
    ///
    /// [(2; 0)-6, (2; 1)-7, (2; 2)-8]
    #[inline]
    pub const fn index(&self, i: Clock, j: Clock) -> usize {
        (i * self.clocks() + j) as usize
    }

    #[inline]
    pub const fn coordinates(&self, index: usize) -> (Clock, Clock) {
        let i = (index as u16 / self.clocks()) as Clock;
        let j = (index as u16 % self.clocks()) as Clock;
        (i, j)
    }

    #[inline]
    fn get(&self, i: Clock, j: Clock) -> Relation {
        self.relations[self.index(i, j)].clone()
    }

    #[inline]
    fn set(&mut self, i: Clock, j: Clock, relation: Relation) {
        let index = self.index(i, j);
        self.relations[index] = relation
    }

    #[inline]
    fn upper(&self, clock: Clock) -> Relation {
        self.relations[self.index(clock, REFERENCE)].clone()
    }

    #[inline]
    fn set_upper(&mut self, clock: Clock, relation: Relation) {
        let index = self.index(clock, REFERENCE);
        self.relations[index] = relation
    }

    #[inline]
    fn lower(&self, clock: Clock) -> Relation {
        self.relations[self.index(REFERENCE, clock)].clone()
    }

    #[inline]
    fn set_lower(&mut self, clock: Clock, relation: Relation) {
        let index = self.index(REFERENCE, clock);
        self.relations[index] = relation
    }

    #[inline]
    fn diagonal(&self, i: Clock, j: Clock) -> Relation {
        self.relations[self.index(i, j)].clone()
    }

    #[inline]
    fn set_diagonal(&mut self, i: Clock, j: Clock, relation: Relation) {
        let index = self.index(i, j);
        self.relations[index] = relation
    }

    #[inline]
    fn empty(mut self) -> DBM<Unsafe> {
        self.set(REFERENCE, REFERENCE, Relation::new(-1, Strictness::Strict));
        DBM {
            clocks: self.clocks,
            relations: self.relations,
            state: Unsafe {},
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        for c in REFERENCE..self.clocks() {
            if self[(c, c)] != ZERO {
                return true;
            }
        }
        false
    }

    pub fn fmt_conjunctions(&self, labels: &Vec<&str>) -> String {
        let mut conjunctions: Vec<String> = Vec::new();

        for i in REFERENCE + 1..self.clocks() {
            // Lower bound: 0 - c R N.
            let lower = self.lower(i);
            if !lower.is_infinity() {
                conjunctions.push(format!(
                    "-{} {} {}",
                    labels[(i - 1) as usize],
                    lower.strictness(),
                    lower.limit()
                ));
            }

            // Upper bound: c - 0 R N.
            let upper = self.upper(i);
            if !upper.is_infinity() {
                conjunctions.push(format!(
                    "{} {} {}",
                    labels[(i - 1) as usize],
                    upper.strictness(),
                    upper.limit()
                ));
            }

            for j in REFERENCE + 1..self.clocks() {
                if i == REFERENCE || j == REFERENCE || i == j {
                    continue;
                }

                let relation = self.diagonal(i, j);
                if relation.is_infinity() {
                    continue;
                }

                // Difference constraints: c0 - c1 R N.
                conjunctions.push(format!(
                    "{} - {} {} {}",
                    labels[(i - 1) as usize],
                    labels[(j - 1) as usize],
                    relation.strictness(),
                    relation.limit()
                ));
            }
        }

        conjunctions.join(" ∧ ")
    }

    pub fn fmt_graphviz_digraph(&self, minimal: BitSet, labels: &Vec<&str>) -> String {
        let mut dot = String::from("digraph G {\n");

        dot.push_str("ranksep=4.0;\n");

        for i in REFERENCE..self.clocks() {
            dot.push_str(&format!("{} [label=\"{}\"];\n", i, labels[i as usize]));
        }

        for i in REFERENCE..self.clocks() {
            for j in REFERENCE..self.clocks() {
                if minimal.test(self.index(i, j)) {
                    dot.push_str(&format!("{} -> {} [label=\"{}\"];\n", i, j, self[(i, j)]));
                }
            }
        }

        dot.push_str("}\n");
        dot
    }
}

impl<T: DBMState> Index<(Clock, Clock)> for DBM<T> {
    type Output = Relation;

    fn index(&self, index: (Clock, Clock)) -> &Self::Output {
        let (i, j) = index;
        &self.relations[self.index(i, j)]
    }
}

#[derive(Clone)]
pub struct Canonical {}
impl DBMState for Canonical {}

impl DBM<Canonical> {
    // Returns the most strictly constrained DBM.
    pub fn zero(clocks: Clock) -> Self {
        let dimension: u16 = clocks + 1;
        Self {
            clocks: dimension,
            relations: vec![ZERO; (dimension * dimension) as usize],
            state: Canonical {},
        }
    }

    // Returns an unconstrained DBM.
    pub fn universe(clocks: Clock) -> Self {
        let dimension: u16 = clocks + 1;
        let mut dbm = Self {
            clocks: dimension,
            relations: vec![INFINITY; (dimension * dimension) as usize],
            state: Canonical {},
        };

        for i in 0..dimension {
            dbm.set_lower(i, ZERO);
            dbm.set_diagonal(i, i, ZERO);
        }

        dbm
    }

    /// Returns a tuple (subset, superset bool) of:
    /// subset is true then self is a subset of other.
    /// superset is true then self is a superset of other.
    /// If both subset and superset then they are equal.
    pub fn relation(&self, other: &Self) -> (bool, bool) {
        let mut subset = true;
        let mut superset = true;

        for i in REFERENCE..self.clocks() {
            for j in REFERENCE..self.clocks() {
                if !subset && !superset {
                    return (subset, superset);
                }

                let lhs = self.diagonal(i, j);
                let rhs = other.diagonal(i, j);

                subset = subset && (lhs <= rhs);
                superset = superset && (lhs >= rhs);
            }
        }

        return (subset, superset);
    }

    /// Returns true if all clocks' upper bound is infinity.
    pub fn can_delay_indefinite(&self) -> bool {
        for i in REFERENCE + 1..self.clocks() {
            if !self.upper(i).is_infinity() {
                return false;
            }
        }
        return true;
    }

    /// The up operation computes the strongest postcondition of a zone with respect to delay.
    /// Afterwards the DBM contains the clock assignments that can be reached from by delay.
    /// up(D) = {u + d | u ∈ D, d ∈ ℝ+}.
    /// This operation preserves the canonical form thereby applying it on a canonical DBM
    /// will result in a new canonical DBM.
    pub fn up(&mut self) {
        for i in REFERENCE..self.clocks() {
            self.set_upper(i, INFINITY);
        }
    }

    /// In contrast to Up, Down computes the weakest precondition of the DBM with respect to delay.
    /// down(D) = {u | u + d ∈ D, d ∈ ℝ+} such that the set of clock assignments that can reach D
    /// by some delay d. Algorithmically, it is computed by setting the lower bound on all individual
    /// clocks to (0, ≤).
    pub fn down(&mut self) {
        for i in REFERENCE..self.clocks() {
            // Only if the lower bound is not already lowered do we lower it.
            // For DBMs where diagonals are valid i.e., they are non-negative
            // then we can assume that only when it is greater than (0, ≤)
            // should it be lowered even further.
            if !self.lower(i).is_zero() {
                self.set_lower(i, ZERO);

                // Now that we have lowered the lower bound on the clock.
                // There may be the possibility that the DBM no longer is cannonical.
                // This is because a diagonal constraint on the clock may represent
                // a easier path to take with less constraint. Because of this we
                // have to close it on its diagonals and maybe further weaken the constraint.
                for j in REFERENCE..self.clocks() {
                    if self.diagonal(i, j) < self.lower(i) {
                        self.set_lower(i, self.diagonal(i, j));
                    }
                }
            }
        }
    }

    /// Removes all constraints on a given clock, i.e., the clock may take any positive value.
    /// This is expressed as {u[x=d] | u ∈ D, d ∈ ℝ+}.
    pub fn free(&mut self, clock: Clock) {
        for i in REFERENCE..self.clocks() {
            if i != clock {
                self.set_diagonal(clock, i, INFINITY);
                self.set_diagonal(i, clock, self.upper(i));
            }
        }
    }

    /// Sets the clock to be assigned to its limit. This is expressed as {u[x=m] | u ∈ D}.
    pub fn reset(&mut self, clock: Clock, limit: Limit) {
        let positive = Relation::new(limit, Strictness::Weak);
        let negative = Relation::new(-limit, Strictness::Weak);
        for i in REFERENCE..self.clocks() {
            self.set_diagonal(clock, i, positive.addition(&self.lower(i)));
            self.set_diagonal(i, clock, self.upper(i).addition(&negative));
        }
    }

    /// Sets the lhs to be equal to the rhs. This is expressed as {u[x=u(y)] | u ∈ D, x ∈ D}
    pub fn copy(&mut self, lhs: Clock, rhs: Clock) {
        if lhs == rhs {
            return;
        }

        for i in REFERENCE..self.clocks() {
            if i != lhs {
                self.set_diagonal(lhs, i, self.get(rhs, i));
                self.set_diagonal(i, lhs, self.get(i, rhs));
            }
        }

        self.set_diagonal(lhs, rhs, ZERO);
        self.set_diagonal(rhs, lhs, ZERO);
    }

    /// Compound addition assignment of the clock "clock := clock + limit".
    pub fn shift(&mut self, clock: Clock, limit: Limit) {
        let positive = Relation::new(limit, Strictness::Weak);
        let negative = Relation::new(-limit, Strictness::Weak);
        for i in REFERENCE..self.clocks() {
            if i != clock {
                let from = self.get(clock, i);
                self.set_diagonal(clock, i, from.addition(&positive));
                let to = self.get(i, clock);
                self.set_diagonal(i, clock, to.addition(&negative));
            }
        }

        if self.lower(clock) > ZERO {
            self.set_lower(clock, ZERO);
        }

        if self.upper(clock) < ZERO {
            self.set_upper(clock, ZERO);
        }
    }

    pub fn satisfies(&self, i: Clock, j: Clock, relation: Relation) -> bool {
        let ij = self[(i, j)].clone();
        let ji = self[(j, i)].clone();
        ij <= relation || ji > relation.negation()
    }

    /// Returns a vector with the length corresponding to each clock in the DBM.
    /// Each group will be assigned a unique index and every clock within the
    /// same group will always be synchronised meaning that the when valuations
    /// are relased for clocks within the same group then the clocks will have
    /// the same values. The second vector is the heads of the different chains.
    pub fn synchronised_clocks(&self) -> (Vec<Clock>, Vec<Clock>) {
        let mut bits = BitSet::with_capacity(self.clocks() as usize);
        let mut chains = vec![0; self.clocks() as usize];
        let mut heads = Vec::with_capacity(self.clocks() as usize);

        for i in REFERENCE..self.clocks() {
            // If the clock has already been assigned to a synchronisation group
            // then we skip it and continue to the next one.
            if bits.test(i as usize) {
                continue;
            }

            // Assigns the group ID k (which is i initially) to the current clock at i.
            let mut k = i;
            heads.push(k);
            bits.set(i as usize, true);

            for j in i + 1..self.clocks() {
                // Check if the difference between the clocks' valuation will always be 0.
                if self[(i, j)].limit() == -self[(j, i)].limit() {
                    // Point back to the previous clock in the chain.
                    chains[k as usize] = j;
                    bits.set(j as usize, true);
                    k = j;
                }
            }

            chains[k as usize] = i;
        }

        (chains, heads)
    }

    // Returns true if an over-approximated intersection was found.
    pub fn maybe_intersects(&self, other: &Self) -> bool {
        if self.clocks() != other.clocks() {
            panic!("inconsistent DBM cardinality")
        }

        for i in REFERENCE + 1..self.clocks() {
            for j in 0..i {
                let ij1 = self.get(i, j);
                if !ij1.is_infinity() && ij1.negation() >= other.get(j, i) {
                    return false;
                }

                let ij2 = other.get(i, j);
                if !ij2.is_infinity() && ij2.negation() >= self.get(j, i) {
                    return false;
                }
            }
        }

        true
    }

    pub fn intersection(self, src: &Self) -> Option<Self> {
        if self.clocks() != src.clocks() {
            panic!("inconsistent DBM cardinality")
        }

        let mut dst = self.dirty();

        for i in REFERENCE..dst.clocks() {
            for j in REFERENCE..dst.clocks() {
                if dst[(i, j)] > src[(i, j)] {
                    dst[(i, j)] = src[(i, j)].clone();
                    if src[(i, j)].negation() >= dst[(j, i)] {
                        return None;
                    }
                }
            }
        }

        match dst.clean() {
            Ok(valid) => Some(valid),
            Err(_) => None,
        }
    }

    pub fn intersects(&self, other: &Self) -> bool {
        self.maybe_intersects(other) && self.clone().intersection(other).is_some()
    }

    pub fn close_ij(mut self, i: Clock, j: Clock) -> Result<DBM<Canonical>, DBM<Unsafe>> {
        if self.clocks <= 2 {
            return Ok(self);
        }

        let ij = self[(i, j)].clone();

        for k in REFERENCE..self.clocks() {
            let jk = self[(j, k)].clone();
            if jk.is_infinity() {
                continue;
            }

            let ik = ij.addition(&jk);
            if self[(i, k)] > ik {
                self.set(i, k, ik);
            }
        }

        for p in REFERENCE..self.clocks() {
            let pi = self[(p, i)].clone();
            if pi.is_infinity() {
                continue;
            }

            let pj = pi.addition(&ij);
            if self[(p, j)] <= pj {
                continue;
            }

            self.set(p, j, pj.clone());

            for q in REFERENCE..self.clocks() {
                let jq = self[(j, q)].clone();
                if jq.is_infinity() {
                    continue;
                }

                let pq = pi.addition(&jq);
                if self[(p, q)] > pq {
                    self.set(p, q, pq);
                }
            }
        }

        if self.is_empty() {
            return Err(self.empty());
        }
        return Ok(self);
    }

    pub fn tighten(
        mut self,
        i: Clock,
        j: Clock,
        relation: Relation,
    ) -> Result<DBM<Canonical>, DBM<Unsafe>> {
        self.set(i, j, relation);
        self.close_ij(i, j)
    }

    pub fn subtraction(self, minued: &Self) -> Vec<DBM<Canonical>> {
        // difference = subtrahend - minued.
        let mut subtrahend = self;
        let mut result = vec![];
        let minimal = subtrahend.minimal();
        let clocks = subtrahend.clocks();

        for i in REFERENCE..clocks {
            for j in REFERENCE..clocks {
                let index = minued.index(i, j);

                // The current relation on two clocks is not required
                // for the minimal representation.
                if !minimal.test(index) {
                    continue;
                }

                if minued[(i, j)] >= subtrahend[(i, j)] {
                    continue;
                }

                let negated = minued[(i, j)].negation();
                match subtrahend.clone().tighten(j, i, negated) {
                    Ok(dbm) => result.push(dbm),
                    Err(_) => panic!("difference failed"),
                }

                match subtrahend.tighten(i, j, minued[(i, j)].clone()) {
                    Ok(dbm) => subtrahend = dbm,
                    Err(_) => panic!("difference failed"),
                }
            }
        }

        result
    }

    // Returns the difference self[(i, j)] - other[(i, j)] if the subtraction is valid and does not violate any constraints.
    // Returns None if the subtraction would violate any constraints (e.g., result in an infeasible system).
    //
    // The function checks whether subtracting self[(i, j)] by other[(i, j)] is still valid given other constraints
    // in the system. The checks ensure that no inconsistency is introduced by the subtraction.
    pub fn minimal_difference(
        &self,
        other: &DBM<Canonical>,
        i: Clock,
        j: Clock,
    ) -> Option<Relation> {
        if self.clocks() != other.clocks() {
            panic!("inconsistent clocks betweem DBMs")
        }

        let self_ij = self[(i, j)].clone();
        let other_ij = other[(i, j)].as_weak();

        for k in REFERENCE..self.clocks() {
            if k == i || k == j {
                continue;
            }

            let self_ik = self[(i, k)].clone();
            let other_kj = other[(k, j)].clone();
            if self_ik.is_infinity() || other_kj.is_infinity() {
                continue;
            }

            // Checks if the subtraction self[(i, j)] - other[(i, j)] is valid with respect to the other constraints,
            // specifically the diagonal constraints. If v >= 0, the subtraction would result in an invalid or inconsistent constraint.
            let v = other_ij.clone() - (self_ik.as_weak() + other_kj.as_weak());
            if v >= ZERO {
                return None;
            }

            let other_ik = other[(i, k)].clone();
            let self_kj = self[(k, j)].clone();
            if other_ik.is_infinity() || self_kj.is_infinity() {
                continue;
            }

            // Same check is performed here but the path taken has swapped DBMs.
            let v = other_ij.clone() - (other_ik.as_weak() + self_kj.as_weak());
            if v >= ZERO {
                return None;
            }
        }

        Some(other_ij - self_ij)
    }

    // Returns a Bitset representing all redundant edges in the DBM.
    // All 0s are redundant but all 1s are required for the minimal representation.
    pub fn minimal(&self) -> BitSet {
        let mut bits = BitSet::with_capacity(self.constraints());

        let (_, heads) = self.synchronised_clocks();
        for i in heads.iter() {
            for j in heads.iter() {
                let ij = self.get(*i, *j);

                for k in heads.iter() {
                    if *k == *i || *k == *j {
                        continue;
                    }

                    let ik = self.get(*i, *k);
                    let kj = self.get(*k, *j);

                    if ik.is_infinity() || kj.is_infinity() {
                        continue;
                    }

                    if ik.addition(&kj) <= ij {
                        // Mark edge (constraint) as redundant.
                        bits.set(self.index(*i, *j) as usize, true);
                    }
                }
            }
        }

        bits.flip_all();
        bits
    }

    pub fn fmt_minimal_graphviz_digraph(&self, labels: &Vec<&str>) -> String {
        let mut minimal = self.minimal();
        for i in REFERENCE..self.clocks() {
            minimal.set(self.index(i, i), false);
        }
        self.fmt_graphviz_digraph(minimal, labels)
    }

    pub fn dirty(self) -> DBM<Dirty> {
        let clocks = self.clocks();
        DBM {
            clocks: self.clocks,
            relations: self.relations,
            state: Dirty::new(clocks),
        }
    }
}

/*pub struct UniformDBM {
    low: DBM<Canonical>,
    high: DBM<Canonical>,
}

impl UniformSampler for UniformDBM {
    type X = DBM<Canonical>;
    
    // [low, high)
    fn new<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized {
        todo!()
    }
    
    // [low, high]
    fn new_inclusive<B1, B2>(low: B1, high: B2) -> Self
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized {
        Self {
            low: low.borrow(),
            high: high.borrow()
        }
    }
    
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        todo!()
    }
}*/

pub struct Unsafe {}
impl DBMState for Unsafe {}

pub struct Dirty {
    flags: BitSet,
}

impl DBMState for Dirty {}

impl Dirty {
    fn new(clocks: Clock) -> Self {
        return Self {
            flags: BitSet::with_capacity((clocks * clocks) as usize),
        };
    }

    pub fn is_touched(&self, index: usize) -> bool {
        self.flags.test(index)
    }

    fn touch(&mut self, clock: Clock) {
        self.flags.set(clock as usize, true);
    }
}

impl DBM<Dirty> {
    pub fn clean(self) -> Result<DBM<Canonical>, DBM<Unsafe>> {
        self.close()
    }

    fn close(mut self) -> Result<DBM<Canonical>, DBM<Unsafe>> {
        for k in REFERENCE..self.clocks() {
            for i in REFERENCE..self.clocks() {
                if i == k {
                    continue;
                }

                for j in REFERENCE..self.clocks() {
                    let ij = self[(i, j)].clone();
                    let ik = self[(i, k)].clone();
                    let kj = self[(k, j)].clone();
                    let ikj = ik.addition(&kj);
                    if ij > ikj {
                        self.set(i, j, ikj);
                    }
                }

                if self[(i, i)] < ZERO {
                    return Err(self.empty());
                }
            }
        }

        return Ok(DBM {
            clocks: self.clocks,
            relations: self.relations,
            state: Canonical {},
        });
    }
}

impl IndexMut<(Clock, Clock)> for DBM<Dirty> {
    fn index_mut(&mut self, clocks: (Clock, Clock)) -> &mut Self::Output {
        let (i, j) = clocks;
        self.state.touch(i);
        self.state.touch(j);
        let index = self.index(i, j);
        &mut self.relations[index]
    }
}

#[cfg(test)]
mod tests {
    use crate::zones::constraint::{Relation, Strictness};

    use super::{Canonical, DBM};

    fn dbm1() -> DBM<Canonical> {
        let mut dbm = DBM::zero(2);
        dbm.set_lower(1, Relation::new(-1, Strictness::Strict));
        dbm.set_upper(1, Relation::new(3, Strictness::Strict));
        dbm.set_lower(2, Relation::new(-2, Strictness::Strict));
        dbm.set_upper(2, Relation::new(3, Strictness::Strict));
        dbm.set_diagonal(1, 2, Relation::new(1, Strictness::Strict));
        dbm.set_diagonal(2, 1, Relation::new(2, Strictness::Strict));
        dbm
    }

    fn dbm2() -> DBM<Canonical> {
        let mut dbm = DBM::zero(2).dirty();
        dbm.set_lower(1, Relation::new(-1, Strictness::Strict));
        dbm.set_upper(1, Relation::new(4, Strictness::Strict));
        dbm.set_lower(2, Relation::new(-2, Strictness::Strict));
        dbm.set_upper(2, Relation::new(4, Strictness::Strict));
        dbm.set_diagonal(1, 2, Relation::new(2, Strictness::Strict));
        dbm.set_diagonal(2, 1, Relation::new(3, Strictness::Strict));

        match dbm.close() {
            Ok(valid) => valid,
            Err(_) => panic!("dbm3 invalid"),
        }
    }

    fn dbm3() -> DBM<Canonical> {
        let mut dbm = DBM::universe(2).dirty();
        dbm.set_upper(1, Relation::new(3, Strictness::Weak));
        dbm.set_upper(2, Relation::new(4, Strictness::Weak));

        match dbm.close() {
            Ok(valid) => valid,
            Err(_) => panic!("dbm3 invalid"),
        }
    }

    fn dbm4() -> DBM<Canonical> {
        let mut dbm = DBM::universe(2).dirty();
        dbm.set_upper(1, Relation::new(1, Strictness::Weak));
        dbm.set_upper(2, Relation::new(2, Strictness::Weak));

        match dbm.close() {
            Ok(valid) => valid,
            Err(_) => panic!("dbm3 invalid"),
        }
    }

    #[test]
    fn fmt_dbm1() {
        let dbm = dbm1();
        println!("{}", dbm.fmt_conjunctions(&vec!["x", "y"]));
        println!("{}", dbm.fmt_minimal_graphviz_digraph(&vec!["0", "x", "y"]));
        assert!(false);
    }

    #[test]
    fn fmt_dbm2() {
        let dbm = dbm2();
        println!("{}", dbm.fmt_conjunctions(&vec!["x", "y"]));
        println!("{}", dbm.fmt_minimal_graphviz_digraph(&vec!["0", "x", "y"]));
        assert!(false);
    }

    #[test]
    fn fmt_dbm3() {
        let dbm = dbm3();
        println!("{}", dbm.fmt_conjunctions(&vec!["x", "y"]));
        println!("{}", dbm.fmt_minimal_graphviz_digraph(&vec!["0", "x", "y"]));
        assert!(false);
    }

    #[test]
    fn fmt_dbm4() {
        let dbm = dbm4();
        println!("{}", dbm.fmt_conjunctions(&vec!["x", "y"]));
        println!("{}", dbm.fmt_minimal_graphviz_digraph(&vec!["0", "x", "y"]));
        assert!(false);
    }

    #[test]
    fn fmt_dbm2_intersection_with_dbm3() {
        let dmb2 = dbm2();
        let dbm3 = dbm3();
        assert!(dmb2.maybe_intersects(&dbm3));
        assert!(dmb2.clone().intersection(&dbm3).is_some());
        let intersection = dmb2.intersection(&dbm3).unwrap();
        println!("{}", intersection.fmt_conjunctions(&vec!["x", "y"]));
        println!(
            "{}",
            intersection.fmt_minimal_graphviz_digraph(&vec!["0", "x", "y"])
        );
        /*let intersection = dmb2.intersection(&dbm3).unwrap();
        println!("{}", intersection.fmt_conjunctions(&vec!["x", "y"]));
        println!("{}", intersection.fmt_minimal_graphviz_digraph(&vec!["0", "x", "y"]));
        assert!(false);*/
    }

    #[test]
    fn fmt_dbm1_subtraction_with_universe() {
        let dbm1 = dbm1();
        let universe = DBM::universe(2);
        let subtractions = universe.subtraction(&dbm1);
        // assert_eq!(4, subtractions.len());
        println!("{}", subtractions[0].fmt_conjunctions(&vec!["x", "y"]));
        println!("{}", subtractions[1].fmt_conjunctions(&vec!["x", "y"]));
        println!("{}", subtractions[2].fmt_conjunctions(&vec!["x", "y"]));
    }

    #[test]
    fn fmt_dbm4_subtraction_with_universe() {
        let dbm4 = dbm4();
        let universe = DBM::universe(2);
        let subtractions = universe.subtraction(&dbm4);
        // assert_eq!(4, subtractions.len());
        println!("{}", subtractions[0].fmt_conjunctions(&vec!["x", "y"]));
        println!("{}", subtractions[1].fmt_conjunctions(&vec!["x", "y"]));
        println!("{}", subtractions[2].fmt_conjunctions(&vec!["x", "y"]));
    }

    #[test]
    fn fmt_dmb1_subtraction_with_dbm4() {
        let dbm1 = dbm1();
        let dbm4 = dbm4();
        let subtractions = dbm1.subtraction(&dbm4);
        assert_eq!(1, subtractions.len());
        println!("{}", subtractions[0].fmt_conjunctions(&vec!["x", "y"]));
    }

    #[test]
    fn synchronised_clocks_configuration_1() {
        let mut dbm = DBM::universe(4);
        dbm.copy(1, 2);
        let (chains, heads) = dbm.synchronised_clocks();
        // Each loop between clocks is a chain:
        // head: @0: 4 -> 0 -> 4
        // head: @1: 2 -> 1 -> 2
        // head: @3: 3 -> 4 -> 3
        // There is three chains in total with heads at 0, 1, and 3.
        assert_eq!(vec![0, 2, 1, 3, 4], chains);
        assert_eq!(vec![0, 1, 3, 4], heads);
    }

    #[test]
    fn synchronised_clocks_configuration_2() {
        let mut dbm = DBM::universe(4);
        dbm.copy(0, 4);
        dbm.copy(1, 2);
        let (chains, heads) = dbm.synchronised_clocks();
        // Each loop between clocks is a chain:
        // head: @0: 4 -> 0 -> 4
        // head: @1: 2 -> 1 -> 2
        // head: @3: 3 -> 4 -> 3
        // There is three chains in total with heads at 0, 1, and 3.
        assert_eq!(vec![4, 2, 1, 3, 0], chains);
        assert_eq!(vec![0, 1, 3], heads);
    }

    #[test]
    fn synchronised_clocks_configuration_3() {
        let mut dbm = DBM::universe(4);
        dbm.copy(1, 2);
        dbm.copy(3, 4);
        let (chains, heads) = dbm.synchronised_clocks();
        // Each loop between clocks is a chain:
        // head: @0: 0 -> 0
        // head: @1: 2 -> 1 -> 2
        // head: @3: 3 -> 4 -> 3
        // There is three chains in total with heads at 0, 1, and 3.
        assert_eq!(vec![0, 2, 1, 4, 3], chains);
        assert_eq!(vec![0, 1, 3], heads);
    }

    #[test]
    fn synchronised_clocks_configuration_4() {
        let mut dbm = DBM::universe(4);
        dbm.copy(2, 1);
        dbm.copy(3, 1);
        dbm.copy(4, 1);
        let (chains, heads) = dbm.synchronised_clocks();
        // Each loop between clocks is a chain:
        // head: @0: 0 -> 0
        // head: @1: 2 -> 3 -> 4 -> 1 -> 2
        // There is three chains in total with heads at 0, 1, and 3.
        assert_eq!(vec![0, 2, 3, 4, 1], chains);
        assert_eq!(vec![0, 1], heads);
    }
}
