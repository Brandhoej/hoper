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
    pub fn clocks(&self) -> Option<Clock> {
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
        if let Some(clocks) = self.clocks() {
            if clocks == dbm.dimensions() {
                panic!("inconsistent clocks in federation and dbm");
            }
        }

        self.dbms.push(dbm);
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
        self.clone().subtraction(other).is_empty()
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
    pub fn shift(self, clock: Clock, limit: Limit) -> Self {
        self.map_mut(|mut dbm| {
            dbm.shift(clock, limit);
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
            if subset || (subset && superset) {
                // The self dbm is a subset or equal of the other.
                self.dbms.swap_remove(i);
            } else if superset {
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
        if self.is_empty() {
            return;
        }

        if self.clocks() != other.clocks() {
            panic!("inconsistent clocks between federations")
        }

        for dbm in other.dbms {
            // If the dbm was not included in self then we append it.
            if !self.remove_subsets(&dbm) {
                self.append(dbm);
            }
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
        if let Some(clocks) = self.clocks() {
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
        Self::universe(self.clocks().unwrap()).subtraction(&self)
    }
}
