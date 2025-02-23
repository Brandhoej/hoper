use std::collections::{hash_map::Entry, HashMap};

use crate::zones::constraint::Clock;

use super::{partitioned_symbol_table::PartitionedSymbol, tioa::TIOA};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Environment {
    // Since inserts only happen at initialisation.
    // Then, maybe, the HashMap is not an appropriate datastructure
    // instead a binary tree or something like it would be better.
    clocks: HashMap<PartitionedSymbol, Clock>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            clocks: HashMap::new(),
        }
    }

    pub fn insert_clock(&mut self, symbol: PartitionedSymbol) -> Clock {
        let clock: Clock = (self.clocks.len() + 1) as Clock;
        match self.clocks.entry(symbol) {
            Entry::Occupied(occupied_entry) => *occupied_entry.get(),
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(clock);
                clock
            }
        }
    }

    pub fn get_clock(&self, symbol: PartitionedSymbol) -> Option<Clock> {
        self.clocks.get(&symbol).cloned()
    }
}

impl<T: TIOA + ?Sized> From<&T> for Environment {
    fn from(value: &T) -> Self {
        let mut environment = Self::new();
        for clock in value.clocks() {
            environment.insert_clock(clock);
        }
        environment
    }
}
