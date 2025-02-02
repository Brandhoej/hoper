use std::ops::{Index, IndexMut};

use bitset::BitSet;

use super::{
    bounds::Bounds,
    constraint::{Clock, Limit, Relation, Strictness, INFINITY, REFERENCE, ZERO},
};

pub trait DBMState: Sized {}

#[derive(Clone, Debug)]
pub struct DBM<State: DBMState> {
    /// The number of clocks inside the DBM.
    clocks: Clock,
    // Q: Maybe an enum describing the internal state can be used to chose between
    //      a SmallVec, boxed slice, or array.
    /// The relations between the clocks.
    relations: Box<[Relation]>,
    /// The internal state important for the current type of DBM.
    state: State,
}

impl<State: DBMState> DBM<State> {
    /// Returns the number of clocks excluding the reference clock.
    pub const fn clocks(&self) -> Clock {
        self.clocks - 1
    }

    /// Returns the number of clocks including the reference clock.
    pub const fn dimensions(&self) -> Clock {
        self.clocks
    }

    pub const fn constraints(&self) -> usize {
        (self.dimensions() * self.dimensions()) as usize
    }

    pub fn relations(&self) -> &Box<[Relation]> {
        &self.relations
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
        (i * self.dimensions() + j) as usize
    }

    #[inline]
    pub const fn coordinates(&self, index: usize) -> (Clock, Clock) {
        let i = (index as u16 / self.dimensions()) as Clock;
        let j = (index as u16 % self.dimensions()) as Clock;
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
    pub fn tightens(&self, i: Clock, j: Clock, relation: Relation) -> bool {
        relation.tightens(self[(i, j)], self[(j, i)])
    }

    #[inline]
    pub fn loosens(&self, i: Clock, j: Clock, relation: Relation) -> bool {
        relation.loosens(self[(i, j)], self[(j, i)])
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

    pub fn lower_relations(&self) -> Vec<Relation> {
        (REFERENCE..self.dimensions())
            .map(|clock| self.lower(clock))
            .collect()
    }

    pub fn upper_relations(&self) -> Vec<Relation> {
        (REFERENCE..self.dimensions())
            .map(|clock| self.upper(clock))
            .collect()
    }

    pub fn delay(&mut self, relation: Relation) {
        if relation.is_infinity() {
            self.up();
        } else if !relation.is_zero() {
            for clock in REFERENCE + 1..self.dimensions() {
                if !self.upper(clock).is_infinity() {
                    self.set_upper(clock, self.upper(clock) + relation);
                }
            }
        }
    }

    /// The up operation computes the strongest postcondition of a zone with respect to delay.
    /// Afterwards the DBM contains the clock assignments that can be reached from by delay.
    /// up(D) = {u + d | u ∈ D, d ∈ ℝ+}.
    /// This operation preserves the canonical form thereby applying it on a canonical DBM
    /// will result in a new canonical DBM.
    pub fn up(&mut self) {
        for i in REFERENCE + 1..self.dimensions() {
            self.set_upper(i, INFINITY);
        }
    }

    /// In contrast to Up, Down computes the weakest precondition of the DBM with respect to delay.
    /// down(D) = {u | u + d ∈ D, d ∈ ℝ+} such that the set of clock assignments that can reach D
    /// by some delay d. Algorithmically, it is computed by setting the lower bound on all individual
    /// clocks to (0, ≤).
    pub fn down(&mut self) {
        for i in REFERENCE + 1..self.dimensions() {
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
                for j in REFERENCE..self.dimensions() {
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
        // FIXME: Allows freeing the reference clock.
        for i in REFERENCE..self.dimensions() {
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
        for i in REFERENCE..self.dimensions() {
            self.set_diagonal(clock, i, positive.addition(&self.lower(i)));
            self.set_diagonal(i, clock, self.upper(i).addition(&negative));
        }
    }

    /// Sets the lhs to be equal to the rhs. This is expressed as {u[x=u(y)] | u ∈ D, x ∈ D}
    pub fn copy(&mut self, lhs: Clock, rhs: Clock) {
        if lhs == rhs {
            return;
        }

        for i in REFERENCE..self.dimensions() {
            if i != lhs {
                self.set_diagonal(lhs, i, self.get(rhs, i));
                self.set_diagonal(i, lhs, self.get(i, rhs));
            }
        }

        self.set_diagonal(lhs, rhs, ZERO);
        self.set_diagonal(rhs, lhs, ZERO);
    }

    /// Compound addition assignment of the clock "clock := clock + relation".
    pub fn shift(&mut self, clock: Clock, relation: Relation) {
        // FIXME: I dont think this handles DBMs which can delay indefinitly correctly.
        let positive = relation;
        let negative = relation.negation();
        for i in REFERENCE..self.dimensions() {
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

    pub fn shift_all(&mut self, relation: Relation) {
        for clock in REFERENCE + 1..self.dimensions() {
            self.shift(clock, relation);
        }
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
        for c in REFERENCE..self.dimensions() {
            if self[(c, c)] != ZERO {
                return true;
            }
        }
        false
    }

    /// Returns true if the DBM is in cannonical form by checking if closing requires changes.
    #[inline]
    pub fn is_closed(&self) -> bool {
        todo!()
    }

    pub fn fmt_conjunctions(&self, labels: &Vec<&str>) -> String {
        let mut conjunctions: Vec<String> = Vec::new();

        for i in REFERENCE + 1..self.dimensions() {
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

            for j in REFERENCE + 1..self.dimensions() {
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

        for i in REFERENCE..self.dimensions() {
            dot.push_str(&format!("{} [label=\"{}\"];\n", i, labels[i as usize]));
        }

        for i in REFERENCE..self.dimensions() {
            for j in REFERENCE..self.dimensions() {
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

#[derive(Clone, Debug)]
pub struct Canonical {}
impl DBMState for Canonical {}

impl DBM<Canonical> {
    // Returns the most strictly constrained DBM.
    pub fn zero(clocks: Clock) -> Self {
        let dimension: u16 = clocks + 1;
        Self {
            clocks: dimension,
            relations: vec![ZERO; (dimension * dimension) as usize].into_boxed_slice(),
            state: Canonical {},
        }
    }

    // Returns an unconstrained DBM.
    pub fn universe(clocks: Clock) -> Self {
        let dimension: u16 = clocks + 1;
        let mut dbm = Self {
            clocks: dimension,
            relations: vec![INFINITY; (dimension * dimension) as usize].into_boxed_slice(),
            state: Canonical {},
        };

        for i in 0..dimension {
            dbm.set_lower(i, ZERO);
            dbm.set_diagonal(i, i, ZERO);
        }

        dbm
    }

    pub fn convex_union(&mut self, other: &Self) {
        for i in REFERENCE..self.dimensions() {
            for j in REFERENCE..other.dimensions() {
                if self[(i, j)] < other[(i, j)] {
                    self.set(i, j, other[(i, j)]);
                }
            }
        }
    }

    /// Returns a tuple (subset, superset bool) of:
    /// subset is true then self is a subset of other.
    /// superset is true then self is a superset of other.
    /// If both subset and superset then they are equal.
    pub fn relation(&self, other: &Self) -> (bool, bool) {
        let mut subset = true;
        let mut superset = true;

        for i in REFERENCE..self.dimensions() {
            for j in REFERENCE..self.dimensions() {
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

    /// Returns true if self is a subset of other.
    pub fn is_subset_of(&self, other: &Self) -> bool {
        let (subset, _) = self.relation(other);
        subset
    }

    /// Returns true if self is a superset of other.
    pub fn is_superset_of(&self, other: &Self) -> bool {
        let (_, superset) = self.relation(other);
        superset
    }

    /// Returns true if all valuations of self are also in other.
    pub fn is_eq(&self, other: &Self) -> bool {
        let (subset, superset) = self.relation(other);
        subset && superset
    }

    pub fn is_different(&self, other: &Self) -> bool {
        let (subset, superset) = self.relation(other);
        !subset && !superset
    }

    /// Returns true if all clocks' upper bound is infinity.
    pub fn can_delay_indefinite(&self) -> bool {
        for i in REFERENCE + 1..self.dimensions() {
            if !self.upper(i).is_infinity() {
                return false;
            }
        }
        return true;
    }

    pub fn satisfies(&self, i: Clock, j: Clock, relation: Relation) -> bool {
        let ij = self[(i, j)].clone();
        let ji = self[(j, i)].clone();
        ij <= relation || ji > relation.negation()
    }

    pub fn equals(&self, clock: Clock, limit: Limit) -> bool {
        self.upper(clock).limit() <= limit && self.lower(clock).limit() <= -limit
    }

    /// Returns a vector with the length corresponding to each clock in the DBM.
    /// Each group will be assigned a unique index and every clock within the
    /// same group will always be synchronised meaning that the when valuations
    /// are relased for clocks within the same group then the clocks will have
    /// the same values. The second vector is the heads of the different chains.
    pub fn synchronised_clocks(&self) -> (Vec<Clock>, Vec<Clock>) {
        let mut bits = BitSet::with_capacity(self.dimensions() as usize);
        let mut chains = vec![0; self.dimensions() as usize];
        let mut heads = Vec::with_capacity(self.dimensions() as usize);

        for i in REFERENCE..self.dimensions() {
            // If the clock has already been assigned to a synchronisation group
            // then we skip it and continue to the next one.
            if bits.test(i as usize) {
                continue;
            }

            // Assigns the group ID k (which is i initially) to the current clock at i.
            let mut k = i;
            heads.push(k);
            bits.set(i as usize, true);

            for j in i + 1..self.dimensions() {
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
        if self.dimensions() != other.dimensions() {
            panic!("inconsistent DBM cardinality")
        }

        for i in REFERENCE + 1..self.dimensions() {
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
        if self.dimensions() != src.dimensions() {
            panic!("inconsistent DBM cardinality")
        }

        let mut dst = self.dirty();

        for i in REFERENCE..dst.dimensions() {
            for j in REFERENCE..dst.dimensions() {
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

        for k in REFERENCE..self.dimensions() {
            let jk = self[(j, k)].clone();
            if jk.is_infinity() {
                continue;
            }

            let ik = ij.addition(&jk);
            if self[(i, k)] > ik {
                self.set(i, k, ik);
            }
        }

        for p in REFERENCE..self.dimensions() {
            let pi = self[(p, i)].clone();
            if pi.is_infinity() {
                continue;
            }

            let pj = pi.addition(&ij);
            if self[(p, j)] <= pj {
                continue;
            }

            self.set(p, j, pj.clone());

            for q in REFERENCE..self.dimensions() {
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

    /// Only if the new relation tightens the existing relation
    /// is the relation updated and closed.
    pub fn tighten(
        mut self,
        i: Clock,
        j: Clock,
        relation: Relation,
    ) -> Result<DBM<Canonical>, DBM<Unsafe>> {
        if self.tightens(i, j, relation) {
            self.set(i, j, relation);
            return self.close_ij(i, j);
        }
        Ok(self)
    }

    /// Only if the new relation loosens the existing relation
    /// is the relation updated and closed.
    pub fn loosen(
        mut self,
        i: Clock,
        j: Clock,
        relation: Relation,
    ) -> Result<DBM<Canonical>, DBM<Unsafe>> {
        if self.loosens(i, j, relation) {
            self.set(i, j, relation);
            return self.close_ij(i, j);
        }
        Ok(self)
    }

    pub fn subtraction(self, minued: &Self) -> Vec<DBM<Canonical>> {
        // difference = subtrahend - minued.
        let mut subtrahend = self;
        let mut result = vec![];
        let minimal = subtrahend.minimal();
        let clocks = subtrahend.dimensions();

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
        if self.dimensions() != other.dimensions() {
            panic!("inconsistent clocks betweem DBMs")
        }

        let self_ij = self[(i, j)].clone();
        let other_ij = other[(i, j)].as_weak();

        for k in REFERENCE..self.dimensions() {
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

    pub fn minimal_bounds(&self) -> Bounds {
        let minimal = self.minimal();
        let mut bounds = Bounds::new();
        for i in REFERENCE..self.dimensions() {
            for j in REFERENCE..self.dimensions() {
                if minimal.test(self.index(i, j)) {
                    bounds = bounds.set(i, j, self[(i, j)]);
                }
            }
        }
        bounds
    }

    pub fn fmt_minimal_graphviz_digraph(&self, labels: &Vec<&str>) -> String {
        let mut minimal = self.minimal();
        for i in REFERENCE..self.dimensions() {
            minimal.set(self.index(i, i), false);
        }
        self.fmt_graphviz_digraph(minimal, labels)
    }

    pub fn dirty(self) -> DBM<Dirty> {
        let clocks = self.dimensions();
        DBM {
            clocks: self.clocks,
            relations: self.relations,
            state: Dirty::new(clocks),
        }
    }

    pub fn expand(&self, expansion: Relation) -> DBM<Canonical> {
        let mut dbm = self.clone().dirty();

        for i in 0..dbm.dimensions() {
            for j in 0..dbm.dimensions() {
                if !dbm[(i, j)].is_infinity() {
                    dbm[(i, j)] += expansion
                };
            }
        }

        for i in 0..dbm.dimensions() {
            // Restore reflexive constraints.
            dbm[(i, i)] = ZERO;
            dbm[(0, i)] = ZERO;
        }

        dbm.clean().ok().unwrap()
    }

    pub fn extrapolate(self, bounds: Bounds) -> Result<Self, DBM<Unsafe>> {
        match self.dirty().extrapolate(bounds) {
            Ok(dbm) => dbm.clean(),
            Err(dbm) => Err(dbm),
        }
    }

    pub fn duration(&self) -> Relation {
        (REFERENCE + 1..self.dimensions())
            .map(|clock| self.upper(clock) + self.lower(clock))
            .min()
            .unwrap()
    }

    pub fn lower_difference(&self, lower: &Vec<Relation>) -> Relation {
        (REFERENCE + 1..self.dimensions())
            .map(|clock| self.lower(clock).subtraction(&lower[clock as usize]))
            .min()
            .unwrap()
    }

    pub fn upper_difference(&self, upper: &Vec<Relation>) -> Relation {
        (REFERENCE + 1..self.dimensions())
            .map(|clock| self.upper(clock).subtraction(&upper[clock as usize]))
            .min()
            .unwrap()
    }
}

pub struct Unsafe {}
impl DBMState for Unsafe {}

pub struct Dirty {
    flags: BitSet,
}

impl DBMState for Dirty {}

impl Dirty {
    pub fn new(clocks: Clock) -> Self {
        return Self {
            flags: BitSet::with_capacity((clocks * clocks) as usize),
        };
    }

    pub fn any_touched(&self) -> bool {
        self.flags.any()
    }

    pub fn is_touched(&self, index: usize) -> bool {
        self.flags.test(index)
    }

    pub fn touched_count(&self) -> usize {
        self.flags.count() as usize
    }

    fn touch(&mut self, clock: Clock) {
        self.flags.set(clock as usize, true);
    }

    fn touch_all(&mut self) {
        self.flags.reset();
        self.flags.flip_all();
    }
}

impl DBM<Dirty> {
    pub fn from_relations(relations: Box<[Relation]>) -> Result<DBM<Dirty>, ()> {
        let mut clocks: usize = 0;
        while clocks * clocks < relations.len() {
            clocks += 1;
        }

        if clocks * clocks != relations.len() {
            return Err(());
        }

        let mut state = Dirty::new(clocks as Clock);
        state.touch_all();

        Ok(Self {
            clocks: clocks as Clock,
            relations,
            state,
        })
    }

    pub fn tighten(&mut self, i: Clock, j: Clock, relation: Relation) {
        if self.tightens(i, j, relation) {
            self[(i, j)] = relation
        }
    }

    pub fn loosen(&mut self, i: Clock, j: Clock, relation: Relation) {
        if self.loosens(i, j, relation) {
            self[(i, j)] = relation
        }
    }

    // TODO: Should also return the delay which was applied. Such that for bounds
    // only affecting the upper bounds should be the same as just delaying the DBM.
    pub fn extrapolate(mut self, bounds: Bounds) -> Result<Self, DBM<Unsafe>> {
        if let Some(clocks) = bounds.clocks() {
            // Check if the bounds describe a DBM with more clocks.
            if self.clocks() < clocks {
                panic!("too small DBM for extrapolating the bounds");
            }
        } else {
            // No clocks requires means that the bounds is empty.
            return Ok(self);
        }

        for ((i, j), relation) in bounds.into_iter() {
            if i == j && relation != ZERO {
                return Err(self.empty());
            }

            if self[(i, j)] != relation {
                self[(i, j)] = relation;
            }
        }

        Ok(self)
    }

    pub fn clean(self) -> Result<DBM<Canonical>, DBM<Unsafe>> {
        // Nothin to clean? Then it must be already closed and cannonical.
        // This relies on the fact, that an unsafe DBM cannot get dirty.
        // Maybe in the future that would be an incorrect assumption.
        if !self.state.any_touched() {
            return Ok(DBM {
                clocks: self.clocks,
                relations: self.relations,
                state: Canonical {},
            });
        }

        self.close()
    }

    fn close(mut self) -> Result<DBM<Canonical>, DBM<Unsafe>> {
        for k in REFERENCE..self.dimensions() {
            for i in REFERENCE..self.dimensions() {
                if i == k {
                    continue;
                }

                for j in REFERENCE..self.dimensions() {
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

        if self.is_empty() {
            panic!("still empty after closure")
        }

        Ok(DBM {
            clocks: self.clocks,
            relations: self.relations,
            state: Canonical {},
        })
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
    use itertools::min;
    use rand::distributions::uniform::UniformSampler;

    use crate::zones::{
        bounds::Bounds,
        constraint::{Relation, RelationsSample, Strictness, UniformRelations, INFINITY, ZERO},
    };

    use super::{Canonical, Dirty, DBM};

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
    fn dmb1_relation() {
        let dbm = dbm1();
        let (subset, superset) = dbm.relation(&dbm);
        assert!(subset);
        assert!(superset);
    }

    #[test]
    fn dmb2_relation() {
        let dbm = dbm2();
        let (subset, superset) = dbm.relation(&dbm);
        assert!(subset);
        assert!(superset);
    }

    #[test]
    fn dmb3_relation() {
        let dbm = dbm3();
        let (subset, superset) = dbm.relation(&dbm);
        assert!(subset);
        assert!(superset);
    }

    #[test]
    fn dmb4_relation() {
        let dbm = dbm4();
        let (subset, superset) = dbm.relation(&dbm);
        assert!(subset);
        assert!(superset);
    }

    #[test]
    fn dmb1_expanded_relation() {
        let dbm = dbm1();
        let expanded = dbm.clone().expand(Relation::new(10, Strictness::Weak));
        let (subset, superset) = dbm.relation(&expanded);
        let (r_subset, r_superset) = expanded.relation(&dbm);
        assert!(subset);
        assert!(!superset);
        assert!(!r_subset);
        assert!(r_superset);
    }

    #[test]
    fn dmb2_expanded_relation() {
        let dbm = dbm2();
        let expanded = dbm.clone().expand(Relation::new(10, Strictness::Weak));
        let (subset, superset) = dbm.relation(&expanded);
        let (r_subset, r_superset) = expanded.relation(&dbm);
        assert!(subset);
        assert!(!superset);
        assert!(!r_subset);
        assert!(r_superset);
    }

    #[test]
    fn dmb3_expanded_relation() {
        let dbm = dbm3();
        let expanded = dbm.clone().expand(Relation::new(10, Strictness::Weak));
        let (subset, superset) = dbm.relation(&expanded);
        let (r_subset, r_superset) = expanded.relation(&dbm);
        assert!(subset);
        assert!(!superset);
        assert!(!r_subset);
        assert!(r_superset);
    }

    #[test]
    fn dmb4_expanded_relation() {
        let dbm = dbm4();
        let expanded = dbm.clone().expand(Relation::new(10, Strictness::Weak));
        let (subset, superset) = dbm.relation(&expanded);
        let (r_subset, r_superset) = expanded.relation(&dbm);
        assert!(subset);
        assert!(!superset);
        assert!(!r_subset);
        assert!(r_superset);
    }

    #[test]
    fn sample_between_zero_and_a_bit_larger() {
        let low = DBM::zero(2);
        let high = low.clone().expand(Relation::new(16, Strictness::Weak));

        let mut rng = rand::thread_rng();
        let sampler = UniformRelations::new_inclusive(
            RelationsSample::new(low.relations().clone().into()),
            RelationsSample::new(high.relations().clone().into()),
        );

        for _ in 0..=10000 {
            let sample = sampler.sample(&mut rng);
            let dbm = DBM::<Dirty>::from_relations(sample.relations().into()).unwrap();
            assert!(dbm.clean().is_ok())
        }
    }

    #[test]
    fn dbm1_subtraction_with_universe() {
        let dbm1 = dbm1();
        let universe = DBM::universe(2);
        let subtractions = universe.subtraction(&dbm1);
        assert_eq!(4, subtractions.len());
    }

    #[test]
    fn dbm2_intersection_with_dbm3() {
        let dmb2 = dbm2();
        let dbm3 = dbm3();
        assert!(dmb2.maybe_intersects(&dbm3));
        assert!(dmb2.clone().intersection(&dbm3).is_some());
    }

    #[test]
    fn dbm4_subtraction_with_universe() {
        let dbm4 = dbm4();
        let universe = DBM::universe(2);
        let subtractions = universe.subtraction(&dbm4);
        assert_eq!(2, subtractions.len());
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

    #[test]
    fn extrapolation_universe_with_delayed_bounds() {
        let dbm = DBM::universe(2);
        let bounds = Bounds::universe(2);
        let extrapolation = dbm.extrapolate(bounds);

        assert!(extrapolation.is_ok());
        assert!(extrapolation.ok().unwrap().is_eq(&DBM::universe(2)))
    }

    #[test]
    fn extrapolate_universe_tighter_bounds() {
        let dbm = DBM::universe(2);
        let bounds = Bounds::universe(2)
            .tighten_lower(1, Relation::weak(-10))
            .tighten_lower(2, Relation::weak(-10))
            .tighten_upper(1, Relation::strict(20))
            .tighten_upper(2, Relation::strict(20));
        let extrapolation = dbm.extrapolate(bounds);

        assert!(extrapolation.is_ok());
        assert_eq!(
            extrapolation
                .ok()
                .unwrap()
                .fmt_conjunctions(&vec!["x", "y"]),
            "-x ≤ -10 ∧ x < 20 ∧ x - y < 10 ∧ -y ≤ -10 ∧ y < 20 ∧ y - x < 10"
        );
    }

    #[test]
    fn delays_from_zero() {
        let mut dbm = DBM::zero(2);
        assert_eq!(dbm.duration(), ZERO);

        dbm.delay(Relation::weak(1));
        assert_eq!(dbm.duration(), Relation::weak(1));

        dbm.delay(Relation::weak(-1));
        assert_eq!(dbm.duration(), ZERO);

        dbm.delay(Relation::weak(10));
        assert_eq!(dbm.duration(), Relation::weak(10));

        dbm.delay(Relation::weak(-5));
        assert_eq!(dbm.duration(), Relation::weak(5));

        dbm.delay(Relation::weak(-1));
        assert_eq!(dbm.duration(), Relation::weak(4));
    }

    #[test]
    fn delays_from_universe() {
        let mut dbm = DBM::universe(2);
        assert_eq!(dbm.duration(), INFINITY);

        dbm.delay(Relation::weak(10));
        assert_eq!(dbm.duration(), INFINITY);

        dbm.delay(Relation::weak(-5));
        assert_eq!(dbm.duration(), INFINITY);
    }

    #[test]
    fn delays_dbm1() {
        let mut dbm = dbm1();
        assert_eq!(dbm.duration(), Relation::strict(1));

        dbm.delay(Relation::weak(4));
        assert_eq!(dbm.duration(), Relation::strict(5));

        dbm.up();
        assert_eq!(dbm.duration(), INFINITY);

        dbm.down();
        assert_eq!(dbm.duration(), INFINITY);

        dbm.free(1);
        assert_eq!(dbm.duration(), INFINITY);

        dbm.reset(1, 10);
        assert_eq!(dbm.duration(), Relation::weak(0));
    }

    #[test]
    fn shifted_zero() {
        let mut dbm = DBM::zero(1);
        let original_lower_relation = dbm.lower_relations();
        assert_eq!("(0, ≤)", original_lower_relation[0].to_string());
        assert_eq!("(0, ≤)", original_lower_relation[1].to_string());

        dbm.shift_all(Relation::weak(10));
        let after_shift_lower_relations = dbm.lower_relations();
        assert_eq!("(0, ≤)", after_shift_lower_relations[0].to_string());
        assert_eq!("(-10, ≤)", after_shift_lower_relations[1].to_string());

        let shifted_by = dbm.lower_difference(&original_lower_relation);
        assert_eq!("(-10, ≤)", shifted_by.to_string());

        dbm.shift_all(Relation::weak(-10));
        assert!(dbm.is_eq(&DBM::zero(1)));
    }

    #[test]
    fn shifted_dbm1() {
        let mut dbm = dbm1();
        let original_lower_relations = dbm.lower_relations();
        assert_eq!("(0, ≤)", original_lower_relations[0].to_string());
        assert_eq!("(-1, <)", original_lower_relations[1].to_string());
        assert_eq!("(-2, <)", original_lower_relations[2].to_string());

        dbm.shift_all(Relation::weak(10));
        let after_shift_lower_relations = dbm.lower_relations();
        assert_eq!("(0, ≤)", after_shift_lower_relations[0].to_string());
        assert_eq!("(-11, <)", after_shift_lower_relations[1].to_string());
        assert_eq!("(-12, <)", after_shift_lower_relations[2].to_string());

        let shifted_by = dbm.lower_difference(&original_lower_relations);
        assert_eq!("(-10, <)", shifted_by.to_string());

        dbm.shift_all(Relation::weak(-10));
        assert!(dbm.is_eq(&dbm1()));
    }

    #[test]
    fn delayed_dbm3() {
        let mut dbm = dbm3();
        let original_upper_relations = dbm.upper_relations();
        assert_eq!("(0, ≤)", original_upper_relations[0].to_string());
        assert_eq!("(3, ≤)", original_upper_relations[1].to_string());

        dbm.delay(Relation::weak(10));
        let after_delay_upper_relations = dbm.upper_relations();
        assert_eq!("(0, ≤)", after_delay_upper_relations[0].to_string());
        assert_eq!("(13, ≤)", after_delay_upper_relations[1].to_string());

        let delayed_by = dbm.upper_difference(&original_upper_relations);
        assert_eq!("(10, <)", delayed_by.to_string());

        dbm.delay(Relation::weak(-10));
        assert!(dbm.is_eq(&dbm3()));
    }

    #[test]
    fn bounds_guards_example_difference_1() {
        // Interval of [2, 5):
        let mut dbm = DBM::zero(1);
        dbm.set_lower(1, Relation::weak(-2));
        dbm.set_upper(1, Relation::strict(5));
        assert_eq!("-x ≤ -2 ∧ x < 5", dbm.fmt_conjunctions(&vec!["x"]));

        // Bounds 1: Describes a guard where x > 3.
        let mut bounds_1 = Bounds::new();
        bounds_1 = bounds_1.set_lower(1, Relation::strict(-3));

        let extrapolation_1 = dbm.clone().extrapolate(bounds_1).ok().unwrap();
        assert_eq!(
            "-x < -3 ∧ x < 5",
            extrapolation_1.fmt_conjunctions(&vec!["x"])
        );

        let lower_difference_1 = extrapolation_1.lower_difference(&dbm.lower_relations());
        assert_eq!("(-1, <)", lower_difference_1.to_string());

        let upper_difference_1 = extrapolation_1.upper_difference(&dbm.upper_relations());
        assert_eq!("(0, ≤)", upper_difference_1.to_string());

        assert_eq!(
            "(2, <)",
            extrapolation_1.duration().to_string(),
            "'x > 3 and x < 5' allows a max delay just less than two"
        );

        // Bounds 2: Describes a guard where x > 4.
        let mut bounds_2 = Bounds::new();
        bounds_2 = bounds_2.set_lower(1, Relation::strict(-4));

        let extrapolation_2 = dbm.clone().extrapolate(bounds_2).ok().unwrap();
        assert_eq!(
            "-x < -4 ∧ x < 5",
            extrapolation_2.fmt_conjunctions(&vec!["x"])
        );

        let lower_difference_2 = extrapolation_2.lower_difference(&dbm.lower_relations());
        assert_eq!("(-2, <)", lower_difference_2.to_string());

        let upper_difference_2 = extrapolation_2.upper_difference(&dbm.upper_relations());
        assert_eq!("(0, ≤)", upper_difference_2.to_string());

        assert_eq!(
            "(1, <)",
            extrapolation_2.duration().to_string(),
            "'x > 4 and x < 5' allows a max delay just less than one"
        );

        assert!(
            lower_difference_1 > lower_difference_2,
            "guard 1 is enabled before guard 2"
        );
        assert!(
            upper_difference_1 == upper_difference_2,
            "guard 1 and guard 2 are enabled to the same point"
        )
    }

    #[test]
    fn bounds_guards_example_difference_2() {
        // Interval of [2, 5):
        let mut dbm = DBM::zero(1);
        dbm.set_lower(1, Relation::weak(-2));
        dbm.set_upper(1, Relation::weak(5));
        assert_eq!("-x ≤ -2 ∧ x ≤ 5", dbm.fmt_conjunctions(&vec!["x"]));

        // Bounds 1: Describes a guard where 3 ≤ x.
        let mut bounds_1 = Bounds::new();
        bounds_1 = bounds_1.set_lower(1, Relation::weak(-3));

        let extrapolation_1 = dbm.clone().extrapolate(bounds_1).ok().unwrap();
        assert_eq!(
            "-x ≤ -3 ∧ x ≤ 5",
            extrapolation_1.fmt_conjunctions(&vec!["x"])
        );

        let lower_difference_1 = extrapolation_1.lower_difference(&dbm.lower_relations());
        assert_eq!("(-1, <)", lower_difference_1.to_string());

        let upper_difference_1 = extrapolation_1.upper_difference(&dbm.upper_relations());
        assert_eq!("(0, ≤)", upper_difference_1.to_string());

        assert_eq!(
            "(2, ≤)",
            extrapolation_1.duration().to_string(),
            "'x > 3 and x ≤ 5' allows a max delay of two"
        );

        // Bounds 2: Describes a guard where x > 4.
        let mut bounds_2 = Bounds::new();
        bounds_2 = bounds_2.set_lower(1, Relation::strict(-4));

        let extrapolation_2 = dbm.clone().extrapolate(bounds_2).ok().unwrap();
        assert_eq!(
            "-x < -4 ∧ x ≤ 5",
            extrapolation_2.fmt_conjunctions(&vec!["x"])
        );

        let lower_difference_2 = extrapolation_2.lower_difference(&dbm.lower_relations());
        assert_eq!("(-2, <)", lower_difference_2.to_string());

        let upper_difference_2 = extrapolation_2.upper_difference(&dbm.upper_relations());
        assert_eq!("(0, ≤)", upper_difference_2.to_string());

        assert_eq!(
            "(1, <)",
            extrapolation_2.duration().to_string(),
            "'x > 4 and x ≤ 5' allows a max delay of one"
        );

        assert!(
            lower_difference_1 > lower_difference_2,
            "guard 1 is enabled before guard 2"
        );
        assert!(
            upper_difference_1 == upper_difference_2,
            "guard 1 and guard 2 are enabled to the same point"
        )
    }

    #[test]
    fn delays() {
        // Interval of [2, 5]:
        let mut dbm = DBM::zero(1);
        dbm.set_lower(1, Relation::weak(-2));
        dbm.set_upper(1, Relation::weak(5));
        assert_eq!("-x ≤ -2 ∧ x ≤ 5", dbm.fmt_conjunctions(&vec!["x"]));
        assert_eq!("(3, ≤)", dbm.duration().to_string());

        dbm.delay(Relation::weak(-1));
        assert_eq!("(2, ≤)", dbm.duration().to_string());

        dbm.delay(Relation::strict(-1));
        assert_eq!("(1, <)", dbm.duration().to_string());

        dbm.delay(Relation::weak(1));
        assert_eq!("(2, <)", dbm.duration().to_string());

        dbm.delay(Relation::weak(-1));
        assert_eq!("(1, <)", dbm.duration().to_string());
    }

    #[test]
    fn example_matching_delays() {
        // Zone 1: Interval of [2, 5]:
        let mut dbm_1 = DBM::zero(1);
        dbm_1.set_lower(1, Relation::weak(-2));
        dbm_1.set_upper(1, Relation::weak(5));
        assert_eq!("-x ≤ -2 ∧ x ≤ 5", dbm_1.fmt_conjunctions(&vec!["x"]));

        // Edge 1: Guard (2, 9]
        let mut edge_1 = dbm_1.minimal_bounds();
        edge_1 = edge_1.tighten_lower(1, Relation::weak(-2));
        edge_1 = edge_1.tighten_upper(1, Relation::weak(9));

        let extrapolation_1 = dbm_1.clone().extrapolate(edge_1).ok().unwrap();
        assert_eq!("(-2, ≤)", dbm_1.lower(1).to_string());
        assert_eq!("(-2, ≤)", extrapolation_1.lower(1).to_string());

        let delay_1 = extrapolation_1.lower_difference(&dbm_1.lower_relations());
        let duration_1 = extrapolation_1.duration();
        assert_eq!(
            "-x ≤ -2 ∧ x ≤ 5",
            extrapolation_1.fmt_conjunctions(&vec!["x"])
        );
        assert_eq!(
            "(3, ≤)",
            duration_1.to_string(),
            "the guard is enabled for exactly 3 time units"
        );
        assert_eq!(
            "(0, ≤)",
            delay_1.to_string(),
            "the guard is immediately enabled"
        );

        // Zone 2: Interval of [2, 8]:
        let mut dbm_2 = DBM::zero(1);
        dbm_2.set_lower(1, Relation::weak(-2));
        dbm_2.set_upper(1, Relation::weak(8));
        assert_eq!("-x ≤ -2 ∧ x ≤ 8", dbm_2.fmt_conjunctions(&vec!["x"]));

        // Edge 2: Guard (4, 6)
        let mut edge_2 = dbm_2.minimal_bounds();
        edge_2 = edge_2.tighten_lower(1, Relation::strict(-4));
        edge_2 = edge_2.tighten_upper(1, Relation::strict(6));

        let extrapolation_2 = dbm_2.clone().extrapolate(edge_2).ok().unwrap();
        assert_eq!("(-2, ≤)", dbm_2.lower(1).to_string());
        assert_eq!("(-4, <)", extrapolation_2.lower(1).to_string());

        let delay_2 = extrapolation_2.lower_difference(&dbm_2.lower_relations());
        let duration_2 = extrapolation_2.duration();
        assert_eq!(
            "-x < -4 ∧ x < 6",
            extrapolation_2.fmt_conjunctions(&vec!["x"])
        );
        assert_eq!(
            "(2, <)",
            duration_2.to_string(),
            "to guard is enabled for exactly 2 time units"
        );
        assert_eq!(
            "(-2, <)",
            delay_2.to_string(),
            "to enable the guard we must delay just less than 2 time units"
        );

        // Q: How long do we have to wait to enable the "slowest" guard?
        // A: The maximum delay of the guards.
        let required_dely = min(vec![delay_1, delay_2]).unwrap();
        // The required delay is "negative" because lower constraints are described with negative limits.
        assert_eq!(
            "(-2, <)",
            required_dely.to_string(),
            "more than a delay of 2 time units are required"
        );

        // Q: What are the corrected durations?
        let durations: Vec<_> = vec![(duration_1, delay_1), (duration_2, delay_2)]
            .into_iter()
            .map(|(duration, delay)| (duration - delay) + required_dely)
            .collect();
        assert_eq!("(1, <)", durations[0].to_string());
        assert_eq!("(2, <)", durations[1].to_string());

        // Q: Is it possible for all edges to be enabled?
        let all_enabled = durations.iter().all(|duration| *duration >= ZERO);
        assert!(all_enabled);

        let mut after_1 = extrapolation_1.clone();
        after_1.shift_all(delay_1 - required_dely);
        assert_eq!("(2, ≤)", (delay_1 - required_dely).to_string());
        assert_eq!(
            "-x < -4 ∧ x ≤ 7",
            after_1.fmt_conjunctions(&vec!["x"]),
            "[2, 5] shifted by (2, ≤) to (4, 7]"
        );
        assert_eq!("(3, <)", after_1.duration().to_string());

        let mut after_2 = extrapolation_2.clone();
        after_2.shift_all(delay_2 - required_dely);
        assert_eq!("(0, ≤)", (delay_2 - required_dely).to_string());
        assert_eq!(
            "-x < -4 ∧ x < 6",
            after_2.fmt_conjunctions(&vec!["x"]),
            "(4, 6)"
        );
        assert_eq!("(2, <)", after_2.duration().to_string());
    }
}
