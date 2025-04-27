use std::{ops::Index, slice, vec::IntoIter};

use crate::zones::dbm::{Canonical, DBM};

use super::{
    channel::Channel,
    tioa::{LocationTree, Traversal},
    tiots::{State, Transition},
};

#[derive(Clone, Debug)]
pub struct HyperState {
    states: Vec<State>,
}

impl HyperState {
    pub fn new(states: Vec<State>) -> Self {
        Self { states }
    }

    pub fn len(&self) -> usize {
        self.states.len()
    }

    pub fn locations(&self) -> Vec<&LocationTree> {
        self.states.iter().map(|state| state.location()).collect()
    }

    pub fn location(&self, index: usize) -> &LocationTree {
        self.states[index].location()
    }

    pub fn zones(&self) -> Vec<&DBM<Canonical>> {
        self.states.iter().map(|state| state.zone()).collect()
    }

    pub fn zone(&self, index: usize) -> &DBM<Canonical> {
        self.states[index].zone()
    }

    pub fn iter(&self) -> slice::Iter<State> {
        self.states.iter()
    }

    pub fn into_iter(self) -> IntoIter<State> {
        self.states.into_iter()
    }
}

impl Index<usize> for HyperState {
    type Output = State;

    fn index(&self, index: usize) -> &Self::Output {
        &self.states[index]
    }
}

#[derive(Clone, Debug)]
pub enum HyperTransition {
    Delay {
        state: HyperState,
    },

    Discrete {
        state: HyperState,
        traversals: Vec<Traversal>,
    },
}

impl HyperTransition {
    pub const fn delay(state: HyperState) -> Self {
        Self::Delay { state }
    }

    pub const fn discrete(state: HyperState, traversals: Vec<Traversal>) -> Self {
        Self::Discrete { state, traversals }
    }

    pub const fn is_delay(&self) -> bool {
        matches!(self, Self::Delay { .. })
    }

    pub const fn is_discrete(&self) -> bool {
        matches!(self, Self::Discrete { .. })
    }
}

impl From<HyperTransition> for Vec<Transition> {
    fn from(value: HyperTransition) -> Self {
        match value {
            HyperTransition::Delay { state } => state.into_iter().map(Transition::delay).collect(),
            HyperTransition::Discrete { state, traversals } => state
                .into_iter()
                .zip(traversals.into_iter())
                .map(|(state, traversal)| Transition::discrete(state, traversal))
                .collect(),
        }
    }
}

/// Hyper Timed Input/Output Transition System (HTIOTS).
pub trait HTIOTS {
    fn initial_state(&self) -> HyperState;
    fn transition(&self, transition: HyperTransition) -> Result<HyperState, ()> {
        match transition {
            HyperTransition::Delay { state } => self.delay(state),
            HyperTransition::Discrete { state, traversals } => self.discrete(state, traversals),
        }
    }
    fn delay(&self, state: HyperState) -> Result<HyperState, ()>;
    fn discrete(&self, state: HyperState, traversals: Vec<Traversal>) -> Result<HyperState, ()>;
    fn is_enabled(&self, transition: HyperTransition) -> Result<bool, ()>;
    fn enabled(&self, state: &HyperState, channels: Vec<Channel>) -> Vec<HyperTransition>;
}
