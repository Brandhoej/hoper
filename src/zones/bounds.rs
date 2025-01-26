use std::collections::{
    hash_map::{Entry, IntoIter},
    HashMap,
};

use super::constraint::{Clock, Relation, INFINITY, REFERENCE};

#[derive(Clone)]
pub struct Bounds {
    relations: HashMap<(Clock, Clock), Relation>,
}

impl Bounds {
    pub fn empty() -> Self {
        Self {
            relations: HashMap::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            relations: HashMap::with_capacity(capacity),
        }
    }

    pub fn delay(clocks: Clock) -> Self {
        let mut bounds = Self::with_capacity(clocks as usize);
        for clock in 1..=clocks {
            bounds.relations.insert((clock, REFERENCE), INFINITY);
        }
        bounds
    }

    pub fn set(&mut self, i: Clock, j: Clock, relation: Relation) {
        self.relations.insert((i, j), relation);
    }

    pub fn set_lower(&mut self, clock: Clock, relation: Relation) {
        self.set(REFERENCE, clock, relation);
    }

    pub fn set_upper(&mut self, clock: Clock, relation: Relation) {
        self.set(clock, REFERENCE, relation);
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

    pub fn tighten(&mut self, i: Clock, j: Clock, relation: Relation) {
        match self.relations.entry((i, j)) {
            Entry::Occupied(mut occupied_entry) => {
                occupied_entry.insert(*occupied_entry.get().min(&relation));
            }
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(relation);
            }
        }
    }

    pub fn tighten_upper(&mut self, clock: Clock, relation: Relation) {
        self.tighten(clock, REFERENCE, relation);
    }

    pub fn tighten_lower(&mut self, clock: Clock, relation: Relation) {
        self.tighten(REFERENCE, clock, relation);
    }

    pub fn loosen(&mut self, i: Clock, j: Clock, relation: Relation) {
        match self.relations.entry((i, j)) {
            Entry::Occupied(mut occupied_entry) => {
                occupied_entry.insert(*occupied_entry.get().max(&relation));
            }
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(relation);
            }
        }
    }

    pub fn loosen_upper(&mut self, clock: Clock, relation: Relation) {
        self.loosen(clock, REFERENCE, relation);
    }

    pub fn loosen_lower(&mut self, clock: Clock, relation: Relation) {
        self.loosen(REFERENCE, clock, relation);
    }

    pub fn set_all(&mut self, bounds: impl Iterator<Item = ((Clock, Clock), Relation)>) {
        for ((i, j), relation) in bounds {
            self.set(i, j, relation);
        }
    }

    pub fn tighten_all(&mut self, bounds: impl Iterator<Item = ((Clock, Clock), Relation)>) {
        for ((i, j), relation) in bounds {
            self.tighten(i, j, relation);
        }
    }

    pub fn loosen_all(&mut self, bounds: impl Iterator<Item = ((Clock, Clock), Relation)>) {
        for ((i, j), relation) in bounds {
            self.loosen(i, j, relation);
        }
    }

    pub fn is_empty(&self) -> bool {
        self.relations.is_empty()
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

#[cfg(test)]
mod tests {
    use crate::zones::constraint::{Relation, INFINITY};

    use super::Bounds;

    #[test]
    fn bounds_empty() {
        let bounds = Bounds::empty();
        assert!(bounds.is_empty());
    }

    #[test]
    fn bounds_delay() {
        let bounds = Bounds::delay(2);
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
        let mut bounds = Bounds::delay(2);
        bounds.tighten_upper(1, Relation::weak(10));
        assert_eq!(bounds.upper(1).unwrap(), Relation::weak(10));
        assert_eq!(bounds.upper(2).unwrap(), INFINITY);
    }

    #[test]
    fn bounds_expand() {
        let mut bounds = Bounds::empty();
        bounds.set_lower(1, Relation::weak(-10));
        bounds.set_upper(1, Relation::weak(20));
        bounds.loosen_lower(1, Relation::weak(-5));
        bounds.loosen_upper(1, Relation::weak(25));
        assert_eq!(bounds.upper(1).unwrap(), Relation::weak(25));
        assert_eq!(bounds.lower(1).unwrap(), Relation::weak(-5));
    }

    #[test]
    fn bounds_shrink() {
        let mut bounds = Bounds::empty();
        bounds.set_lower(1, Relation::weak(-5));
        bounds.set_upper(1, Relation::weak(25));
        bounds.tighten_lower(1, Relation::weak(-10));
        bounds.tighten_upper(1, Relation::weak(20));
        assert_eq!(bounds.upper(1).unwrap(), Relation::weak(20));
        assert_eq!(bounds.lower(1).unwrap(), Relation::weak(-10));
    }
}
