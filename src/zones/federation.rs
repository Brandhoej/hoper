use std::vec;

use super::{
    constraint::{Clock, Limit, Relation, Strictness, REFERENCE},
    dbm::{Canonical, DBM},
};

#[derive(Clone)]
pub struct Federation {
    dbms: Vec<DBM<Canonical>>,
}

impl Federation {
    #[inline]
    pub fn new(dbms: Vec<DBM<Canonical>>) -> Federation {
        let mut iterator = dbms.iter();
        if let Some(first) = iterator.next() {
            for dbm in iterator {
                if dbm.dimensions() != first.dimensions() {
                    panic!("inconsistent dimension between federation and DBM")
                }
            }
        }

        Federation { dbms }
    }

    #[inline]
    pub fn zero(clocks: Clock) -> Self {
        Self::new(vec![DBM::zero(clocks)])
    }

    #[inline]
    pub fn universe(clocks: Clock) -> Federation {
        Federation::new(vec![DBM::universe(clocks)])
    }

    #[inline]
    pub fn empty(clocks: Clock) -> Federation {
        Federation::new(vec![])
    }

    #[inline]
    pub fn dimensions(&self) -> Option<Clock> {
        match self.dbms.first() {
            Some(dbm) => Some(dbm.dimensions()),
            None => None,
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.dbms.len() == 0
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.dbms.len()
    }

    #[inline]
    pub fn append(&mut self, dbm: DBM<Canonical>) {
        if let Some(dimensions) = self.dimensions() {
            if dimensions != dbm.dimensions() {
                panic!("inconsistent clocks in federation and dbm");
            }
        }

        // If the dbm was not included in self then we append it.
        let included = self.remove_subsets(&dbm);
        if !included {
            self.dbms.push(dbm.clone());
        }
    }

    #[inline]
    pub fn can_delay_indefinite(&self) -> bool {
        self.dbms.iter().any(|dbm| dbm.can_delay_indefinite())
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &DBM<Canonical>> {
        self.dbms.iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut DBM<Canonical>> {
        self.dbms.iter_mut()
    }

    #[inline]
    pub fn filter_map_mut<F>(self, f: F) -> Self
    where
        F: FnMut(DBM<Canonical>) -> Option<DBM<Canonical>>,
    {
        return Self::new(self.dbms.into_iter().filter_map(f).collect());
    }

    #[inline]
    pub fn map_mut<F>(self, f: F) -> Self
    where
        F: FnMut(DBM<Canonical>) -> DBM<Canonical>,
    {
        return Self::new(self.dbms.into_iter().map(f).collect());
    }

    #[inline]
    pub fn tighten_relation(self, i: Clock, j: Clock, relation: Relation) -> Self {
        self.filter_map_mut(move |dbm| match dbm.tighten(i, j, relation) {
            Ok(dbm) => Some(dbm),
            Err(_) => None,
        })
    }

    #[inline]
    pub fn up(self) -> Self {
        self.map_mut(|mut dbm| {
            dbm.up();
            dbm
        })
    }

    #[inline]
    pub fn down(self) -> Self {
        self.map_mut(|mut dbm| {
            dbm.down();
            dbm
        })
    }

    #[inline]
    pub fn tighten_limit(self, i: Clock, j: Clock, limit: Limit) -> Self {
        self.tighten_relation(i, j, Relation::new(limit, Strictness::Weak))
            .tighten_relation(j, i, Relation::new(-limit, Strictness::Weak))
    }

    #[inline]
    pub fn clear(mut self) -> Self {
        self.dbms.clear();
        self
    }

    #[inline]
    pub fn tighten_upper(self, clock: Clock, relation: Relation) -> Self {
        self.tighten_relation(clock, REFERENCE, relation)
    }

    #[inline]
    pub fn tighten_lower(self, clock: Clock, relation: Relation) -> Self {
        self.tighten_relation(REFERENCE, clock, relation)
    }

    #[inline]
    pub fn is_subset(&self, other: &Self) -> bool {
        if self
            .dbms
            .iter()
            .all(|inner| other.dbms.iter().any(|outer| inner.is_subset_of(outer)))
        {
            return true;
        }

        self.clone().subtraction(other).is_empty()
    }

    #[inline]
    pub fn includes(&self, other: &Self) -> bool {
        other.is_subset(self)
    }

    #[inline]
    pub fn includes_dbm(&self, other: &DBM<Canonical>) -> bool {
        if self.dbms.iter().any(|inner| inner.is_superset_of(other)) {
            return true;
        }

        Federation::new(vec![other.clone()])
            .clone()
            .subtraction(self)
            .is_empty()
    }

    #[inline]
    pub fn free(self, clock: Clock) -> Self {
        self.map_mut(|mut dbm| {
            dbm.free(clock);
            dbm
        })
    }

    #[inline]
    pub fn reset(self, clock: Clock, limit: Limit) -> Self {
        self.map_mut(|mut dbm| {
            dbm.reset(clock, limit);
            dbm
        })
    }

    #[inline]
    pub fn copy(self, lhs: Clock, rhs: Clock) -> Self {
        self.map_mut(|mut dbm| {
            dbm.copy(lhs, rhs);
            dbm
        })
    }

    #[inline]
    pub fn shift(self, clock: Clock, relation: Relation) -> Self {
        self.map_mut(|mut dbm| {
            dbm.shift(clock, relation);
            dbm
        })
    }

    pub fn fmt_disjunctions(&self, labels: &Vec<&str>) -> String {
        let mut disjunctions: Vec<String> = Vec::new();

        for dbm in self.dbms.iter() {
            let conjunctions = dbm.fmt_conjunctions(labels);
            if conjunctions.len() > 0 {
                disjunctions.push(format!("({})", conjunctions));
            }
        }

        disjunctions.join(" ∨ ")
    }

    /// Removes all the DBMs from the self federation which
    /// contain (is a subset or is equal to) the other dbm.
    /// Returns true if the other dbm was a superset of any existing DBMs in self.
    fn remove_subsets(&mut self, other: &DBM<Canonical>) -> bool {
        let mut included = false;
        let mut i = 0;
        while i < self.len() {
            let (subset, superset) = self.dbms[i].relation(&other);
            if subset {
                // The self dbm is a subset or equal to the other.
                self.dbms.swap_remove(i);
            } else if superset || (subset && superset) {
                // The self dbm is a superset of the other.
                included = true;
                i += 1
            } else {
                i += 1
            }
        }

        included
    }

    pub fn union(&mut self, other: Self) {
        if other.is_empty() {
            return;
        }

        if !self.is_empty() && self.dimensions() != other.dimensions() {
            panic!("inconsistent clocks between federations")
        }

        for dbm in other.dbms {
            self.append(dbm);
        }
    }

    pub fn intersect(self, operand: &DBM<Canonical>) -> Self {
        let mut intersection = Self::new(Vec::with_capacity(self.dbms.len()));

        for dbm in self.dbms {
            match dbm.intersection(operand) {
                Some(dbm) => intersection.dbms.push(dbm),
                None => continue,
            }
        }

        intersection
    }

    pub fn intersection(mut self, other: Self) -> Self {
        if self.is_empty() {
            return self;
        }

        for dbm in other.dbms.iter() {
            self = self.intersect(dbm)
        }

        self
    }

    pub fn subtract(self, minued: &DBM<Canonical>) -> Self {
        if let Some(clocks) = self.dimensions() {
            if clocks != minued.dimensions() {
                panic!("inconsistent number of clocks in federation and DBM")
            }
        }

        // We assume that the difference after subtraction has doubled.
        let mut difference = Self::new(Vec::with_capacity(self.dbms.len() * 2));

        for dbm in self.dbms {
            // No subtraction is guarateed to happen so jsut push the original dbm.
            if !dbm.maybe_intersects(&minued) {
                difference.dbms.push(dbm);
                continue;
            }

            difference.union(Self::new(dbm.subtraction(&minued)));
        }

        difference
    }

    pub fn subtraction(mut self, other: &Self) -> Self {
        // This is like subtracting nothing which does nothing.
        if other.is_empty() {
            return self;
        }

        // When subtracting from nothing we get the inverse
        // of what we are trying to subtract.
        if self.is_empty() {
            return other.clone().inverse();
        }

        // If both are not empty. Then we subtract each DBM in other.
        for dbm in other.dbms.iter() {
            self = self.subtract(dbm)
        }

        self
    }

    pub fn inverse(self) -> Self {
        Self::universe(self.dimensions().unwrap()).subtraction(&self)
    }
}

impl From<DBM<Canonical>> for Federation {
    fn from(dbm: DBM<Canonical>) -> Self {
        if dbm.is_empty() {
            return Federation::empty(dbm.clocks());
        }
        Federation::new(vec![dbm])
    }
}

#[cfg(test)]
mod tests {
    use crate::zones::{
        constraint::{Relation, INFINITY},
        dbm::DBM,
        federation::Federation,
    };

    #[test]
    fn regression_1() {
        // Story: The Refinement did not terminate. Exploration found that the federation
        //   when calling append with a DBM did not guarantee to include the DBM afterwards.
        // Federation: "(-x ≤ 0 ∧ x - y ≤ 0 ∧ -y ≤ 0 ∧ y - x ≤ 0)"
        // DBM: "-x ≤ -2 ∧ x - y ≤ 0 ∧ -y ≤ -2 ∧ y - x ≤ 0"
        // It looks like that DBM::relation states that the DBM in the federation is a superset of the DBM.
        //   This is crealy incorrect as they are two points not laying on eachother.

        let mut dbm1_dirty = DBM::zero(2).dirty();
        dbm1_dirty[(0, 0)] = Relation::weak(0);
        dbm1_dirty[(0, 1)] = Relation::weak(0);
        dbm1_dirty[(0, 2)] = Relation::weak(0);
        dbm1_dirty[(1, 0)] = INFINITY;
        dbm1_dirty[(1, 1)] = Relation::weak(0);
        dbm1_dirty[(1, 2)] = Relation::weak(0);
        dbm1_dirty[(2, 0)] = INFINITY;
        dbm1_dirty[(2, 1)] = Relation::weak(0);
        dbm1_dirty[(2, 2)] = Relation::weak(0);
        let dbm1 = dbm1_dirty.clean().ok().unwrap();

        let mut dbm2_dirty = DBM::zero(2).dirty();
        dbm2_dirty[(0, 0)] = Relation::weak(0);
        dbm2_dirty[(0, 1)] = Relation::weak(-2);
        dbm2_dirty[(0, 2)] = Relation::weak(-2);
        dbm2_dirty[(1, 0)] = INFINITY;
        dbm2_dirty[(1, 1)] = Relation::weak(0);
        dbm2_dirty[(1, 2)] = Relation::weak(0);
        dbm2_dirty[(2, 0)] = INFINITY;
        dbm2_dirty[(2, 1)] = Relation::weak(0);
        dbm2_dirty[(2, 2)] = Relation::weak(0);
        let dbm2 = dbm2_dirty.clean().ok().unwrap();

        assert_eq!(
            "-x ≤ 0 ∧ x - y ≤ 0 ∧ -y ≤ 0 ∧ y - x ≤ 0",
            dbm1.fmt_conjunctions(&vec!["x", "y"])
        );
        assert_eq!(
            "-x ≤ -2 ∧ x - y ≤ 0 ∧ -y ≤ -2 ∧ y - x ≤ 0",
            dbm2.fmt_conjunctions(&vec!["x", "y"])
        );

        assert!(dbm1.is_subset_of(&dbm1));
        assert!(dbm2.is_subset_of(&dbm2));

        assert!(dbm2.is_subset_of(&dbm1));
        assert!(!dbm1.is_subset_of(&dbm2));

        assert!(!dbm2.is_superset_of(&dbm1));
        assert!(dbm1.is_superset_of(&dbm2));

        let mut federation = Federation::new(vec![dbm1]);
        assert!(federation.includes_dbm(&dbm2));

        federation.append(dbm2.clone());
        assert!(federation.includes_dbm(&dbm2));
    }
}
