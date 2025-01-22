use std::collections::HashMap;

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

    pub fn insert(&mut self, state: State) {
        let (state_location, state_federation) = state.decompose();
        if let Some(federation) = self.states.get_mut(&state_location) {
            federation.union(state_federation);
        } else {
            self.states.insert(state_location, state_federation);
        }
    }

    pub fn try_insert(&mut self, state: State) -> bool {
        if !self.contains(state.clone()) {
            self.insert(state);
            true
        } else {
            false
        }
    }

    pub fn contains(&self, state: State) -> bool {
        if let Some(federation) = self.states.get(state.location()) {
            state.federation().is_subset(federation)
        } else {
            false
        }
    }
}
