use std::collections::{hash_map::Entry, HashMap};

use crate::zones::dbm::{Canonical, DBM};

use super::{tioa::LocationTree, tiots::State};

pub struct StateSet {
    // Maybe it should be a federation?
    states: HashMap<LocationTree, DBM<Canonical>>,
}

impl StateSet {
    pub fn new() -> Self {
        Self {
            states: HashMap::new(),
        }
    }

    pub fn insert(&mut self, state: &State) {
        match self.states.entry(state.location().clone()) {
            Entry::Occupied(mut occupied_entry) => {
                occupied_entry.get_mut().convex_union(state.ref_zone());
            }
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(state.ref_zone().clone());
            }
        };
    }

    pub fn contains(&self, state: &State) -> bool {
        if let Some(zone) = self.states.get(state.location()) {
            state.ref_zone().is_subset_of(zone)
        } else {
            false
        }
    }
}
