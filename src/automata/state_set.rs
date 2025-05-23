use std::collections::{hash_map::Entry, HashMap};

use crate::zones::federation::Federation;

use super::{tioa::LocationTree, tiots::State};

pub struct StateSet {
    states: HashMap<LocationTree, Federation>,
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
                occupied_entry.get_mut().append(state.zone().clone());
            }
            Entry::Vacant(vacant_entry) => {
                let federation = Federation::new(vec![state.zone().clone()]);
                vacant_entry.insert(federation);
            }
        };
    }

    pub fn contains(&self, state: &State) -> bool {
        if let Some(federation) = self.states.get(state.location()) {
            federation.includes_dbm(state.zone())
        } else {
            false
        }
    }
}
