use std::collections::{hash_map::Entry, HashMap};

use crate::zones::federation::Federation;

use super::{htiots::HyperState, tioa::LocationTree};

pub struct HyperStateSet {
    states: HashMap<Vec<LocationTree>, Vec<Federation>>,
}

impl HyperStateSet {
    pub fn new() -> Self {
        Self {
            states: HashMap::new(),
        }
    }

    pub fn insert(&mut self, state: &HyperState) {
        let locations: Vec<LocationTree> = state
            .locations()
            .into_iter()
            .map(|location| location.clone())
            .collect();
        match self.states.entry(locations) {
            Entry::Occupied(mut occupied_entry) => {
                if occupied_entry.get().len() != state.len() {
                    panic!("attempting to update entry with state tuple of inconsistent length")
                }

                for (idx, federation) in occupied_entry.get_mut().iter_mut().enumerate() {
                    federation.append(state.zone(idx).clone());
                }
            }
            Entry::Vacant(vacant_entry) => {
                let federations: Vec<Federation> = state
                    .iter()
                    .map(|state| Federation::new(vec![state.zone().clone()]))
                    .collect();
                vacant_entry.insert(federations);
            }
        }
    }

    pub fn contains(&self, state: &HyperState) -> bool {
        let locations: Vec<LocationTree> = state
            .locations()
            .into_iter()
            .map(|location| location.clone())
            .collect();
        if let Some(federations) = self.states.get(&locations) {
            federations
                .iter()
                .enumerate()
                .all(|(idx, federation)| federation.includes_dbm(state.zone(idx)))
        } else {
            false
        }
    }

    /// Returns the set of hyper states which represents the yet uncovered part of the state.
    pub fn uncovered(&self, state: &HyperState) -> Vec<HyperState> {
        todo!()
    }
}
