use std::vec;

use super::{
    constraint::{Clock, Limit, Relation, Strictness, REFERENCE},
    dbm::{Canonical, DBM},
};

#[derive(Clone)]
pub struct Federation {
    clocks: Clock,
    dbms: Vec<DBM<Canonical>>,
}

impl Federation {
    #[inline]
    pub fn new(clocks: Clock, dbms: Vec<DBM<Canonical>>) -> Federation {
        for dbm in dbms.iter() {
            if dbm.clocks() != clocks {
                panic!("inconsistent dimension between federation and DBM")
            }
        }

        Federation { clocks, dbms }
    }

    #[inline]
    pub fn zero(clocks: Clock) -> Self {
        Self::new(clocks, vec![DBM::zero(clocks)])
    }

    #[inline]
    pub fn universe(clocks: Clock) -> Federation {
        Federation::new(clocks, vec![DBM::universe(clocks)])
    }

    #[inline]
    pub fn empty(clocks: Clock) -> Federation {
        Federation::new(clocks, vec![])
    }

    #[inline]
    pub const fn clocks(&self) -> Clock {
        self.clocks
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
        if dbm.clocks() != self.clocks() {
            panic!("inconsistent clocks in federation and dbm");
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
        return Self::new(self.clocks(), self.dbms.into_iter().filter_map(f).collect());
    }

    #[inline]
    pub fn tighten_relation(self, i: Clock, j: Clock, relation: Relation) -> Self {
        self.filter_map_mut(move |dbm| match dbm.tighten(i, j, relation) {
            Ok(dbm) => Some(dbm),
            Err(_) => None,
        })
    }

    #[inline]
    pub fn tighten_limit(self, i: Clock, j: Clock, limit: Limit) -> Self {
        self.tighten_relation(i, j, Relation::new(limit, Strictness::Weak))
            .tighten_relation(j, i, Relation::new(-limit, Strictness::Weak))
    }

    pub fn clear(mut self) -> Self {
        self.dbms.clear();
        self
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
        if self.clocks() != other.clocks() {
            panic!("inconsistent clocks between federations")
        }

        if self.is_empty() {
            return;
        }

        for dbm in other.dbms {
            // If the dbm was not included in self then we append it.
            if !self.remove_subsets(&dbm) {
                self.append(dbm);
            }
        }
    }

    pub fn intersect(self, operand: &DBM<Canonical>) -> Self {
        let mut intersection = Self::new(self.clocks(), Vec::with_capacity(self.dbms.len()));

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
        if self.clocks() != minued.clocks() {
            panic!("inconsistent number of clocks in federation and DBM")
        }

        // We assume that the difference after subtraction has doubled.
        let mut difference = Self::new(self.clocks(), Vec::with_capacity(self.dbms.len() * 2));

        for dbm in self.dbms {
            // No subtraction is guarateed to happen so jsut push the original dbm.
            if !dbm.maybe_intersects(&minued) {
                difference.dbms.push(dbm);
                continue;
            }

            difference.union(Self::new(difference.clocks(), dbm.subtraction(&minued)));
        }

        difference
    }

    pub fn subtraction(mut self, other: Self) -> Self {
        // This is like subtracting nothing which does nothing.
        if other.is_empty() {
            return self;
        }

        // When subtracting from nothing we get the inverse
        // of what we are trying to subtract.
        if self.is_empty() {
            return other.inverse();
        }

        // If both are not empty. Then we subtract each DBM in other.
        for dbm in other.dbms.iter() {
            self = self.subtract(dbm)
        }

        self
    }

    pub fn inverse(self) -> Self {
        Self::universe(self.clocks()).subtraction(self)
    }
}
