use std::collections::{
    hash_map::{Entry, IntoIter},
    HashMap,
};

use super::constraint::{Clock, Constraint, Limit, Relation, INFINITY, REFERENCE};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Bounds {
    relations: HashMap<(Clock, Clock), Relation>,
}

impl Bounds {
    pub fn new() -> Self {
        Self {
            relations: HashMap::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            relations: HashMap::with_capacity(capacity),
        }
    }

    pub fn universe(clocks: Clock) -> Self {
        let mut bounds = Self::with_capacity(clocks as usize);
        for clock in 1..=clocks {
            bounds.relations.insert((clock, REFERENCE), INFINITY);
        }
        bounds
    }

    pub fn set(mut self, i: Clock, j: Clock, relation: Relation) -> Self {
        self.relations.insert((i, j), relation);
        self
    }

    pub fn set_lower(self, clock: Clock, relation: Relation) -> Self {
        self.set(REFERENCE, clock, relation)
    }

    pub fn set_upper(self, clock: Clock, relation: Relation) -> Self {
        self.set(clock, REFERENCE, relation)
    }

    pub fn get(&self, i: Clock, j: Clock) -> Option<Relation> {
        self.relations.get(&(i, j)).cloned()
    }

    pub fn upper(&self, clock: Clock) -> Option<Relation> {
        self.get(clock, REFERENCE)
    }

    pub fn lower(&self, clock: Clock) -> Option<Relation> {
        self.get(REFERENCE, clock)
    }

    pub fn tighten(mut self, i: Clock, j: Clock, relation: Relation) -> Self {
        match self.relations.entry((i, j)) {
            Entry::Occupied(mut occupied_entry) => {
                occupied_entry.insert(*occupied_entry.get().min(&relation));
            }
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(relation);
            }
        }
        self
    }

    pub fn tighten_upper(self, clock: Clock, relation: Relation) -> Self {
        self.tighten(clock, REFERENCE, relation)
    }

    pub fn tighten_lower(self, clock: Clock, relation: Relation) -> Self {
        self.tighten(REFERENCE, clock, relation)
    }

    pub fn set_limit(mut self, clock: Clock, limit: Limit) -> Self {
        self = self.set_upper(clock, Relation::weak(limit));
        self.set_lower(clock, Relation::weak(-limit))
    }

    pub fn set_difference_limit(mut self, i: Clock, j: Clock, limit: Limit) -> Self {
        self = self.set(i, j, Relation::weak(limit));
        self.set(j, i, Relation::weak(limit))
    }

    pub fn loosen(mut self, i: Clock, j: Clock, relation: Relation) -> Self {
        match self.relations.entry((i, j)) {
            Entry::Occupied(mut occupied_entry) => {
                occupied_entry.insert(*occupied_entry.get().max(&relation));
            }
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(relation);
            }
        }
        self
    }

    pub fn loosen_upper(self, clock: Clock, relation: Relation) -> Self {
        self.loosen(clock, REFERENCE, relation)
    }

    pub fn loosen_lower(self, clock: Clock, relation: Relation) -> Self {
        self.loosen(REFERENCE, clock, relation)
    }

    pub fn set_all(mut self, bounds: impl Iterator<Item = ((Clock, Clock), Relation)>) -> Self {
        for ((i, j), relation) in bounds {
            self = self.set(i, j, relation);
        }
        self
    }

    pub fn tighten_all(mut self, bounds: impl Iterator<Item = ((Clock, Clock), Relation)>) -> Self {
        for ((i, j), relation) in bounds {
            self = self.tighten(i, j, relation);
        }
        self
    }

    pub fn loosen_all(mut self, bounds: impl Iterator<Item = ((Clock, Clock), Relation)>) -> Self {
        for ((i, j), relation) in bounds {
            self = self.loosen(i, j, relation);
        }
        self
    }

    pub fn negation(mut self) -> Self {
        self.relations
            .values_mut()
            .for_each(|relation| *relation = relation.negation());
        self
    }

    pub fn is_empty(&self) -> bool {
        self.relations.is_empty()
    }

    pub fn clear(mut self) -> Self {
        self.relations.clear();
        self
    }

    /// Returns the minimum required number of clocks a DBM should have for it
    /// to be able to extrapolate on the bounds.
    pub fn clocks(&self) -> Option<Clock> {
        // Given that the REFERENCE clock is 0. Then the
        // maximum clock value is the required number of
        // clocks a DBM would need to represent the bounds.
        self.relations
            .iter()
            .map(|((i, j), _)| std::cmp::max(*i, *j))
            .max()
    }
}

impl IntoIterator for Bounds {
    type Item = ((Clock, Clock), Relation);
    type IntoIter = IntoIter<(Clock, Clock), Relation>;

    fn into_iter(self) -> Self::IntoIter {
        self.relations.into_iter()
    }
}

impl From<Vec<Constraint>> for Bounds {
    fn from(constraints: Vec<Constraint>) -> Self {
        let mut bounds = Bounds::new();
        for constraint in constraints.into_iter() {
            bounds = bounds.set(
                constraint.minuend(),
                constraint.subtrahend(),
                constraint.relation(),
            )
        }
        bounds
    }
}

#[cfg(test)]
mod tests {
    use crate::zones::constraint::{Relation, INFINITY};

    use super::Bounds;

    #[test]
    fn bounds_empty() {
        let bounds = Bounds::new();
        assert!(bounds.is_empty());
    }

    #[test]
    fn bounds_delay() {
        let bounds = Bounds::universe(2);
        assert!(bounds.clocks().is_some());
        assert_eq!(bounds.clocks().unwrap(), 2);
        assert_eq!(bounds.relations.len(), 2);
        assert!(bounds.upper(1).is_some());
        assert!(bounds.upper(2).is_some());
        assert_eq!(bounds.upper(1).unwrap(), INFINITY);
        assert_eq!(bounds.upper(2).unwrap(), INFINITY);
    }

    #[test]
    fn bounds_tighten_delay() {
        let bounds = Bounds::universe(2).tighten_upper(1, Relation::weak(10));
        assert_eq!(bounds.upper(1).unwrap(), Relation::weak(10));
        assert_eq!(bounds.upper(2).unwrap(), INFINITY);
    }

    #[test]
    fn bounds_expand() {
        let bounds = Bounds::new()
            .set_lower(1, Relation::weak(-10))
            .set_upper(1, Relation::weak(20))
            .loosen_lower(1, Relation::weak(-5))
            .loosen_upper(1, Relation::weak(25));
        assert_eq!(bounds.upper(1).unwrap(), Relation::weak(25));
        assert_eq!(bounds.lower(1).unwrap(), Relation::weak(-5));
    }

    #[test]
    fn bounds_shrink() {
        let bounds = Bounds::new()
            .set_lower(1, Relation::weak(-5))
            .set_upper(1, Relation::weak(25))
            .tighten_lower(1, Relation::weak(-10))
            .tighten_upper(1, Relation::weak(20));
        assert_eq!(bounds.upper(1).unwrap(), Relation::weak(20));
        assert_eq!(bounds.lower(1).unwrap(), Relation::weak(-10));
    }
}
