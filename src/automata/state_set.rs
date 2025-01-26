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
        let (location, zone) = state.decompose();
        if let Some(federation) = self.states.get_mut(&location) {
            federation.append(zone);
        } else {
            self.states.insert(location, zone.into());
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
        let (location, zone) = state.decompose();
        if let Some(federation) = self.states.get(&location) {
            federation.includes(&zone.into())
        } else {
            false
        }
    }
}
