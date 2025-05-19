use std::{
    ops::{Index, IndexMut},
    slice,
    vec::IntoIter,
};

use itertools::{
    Either::{Left, Right},
    Itertools,
};

use crate::zones::{
    dbm::{Canonical, DBM},
    window::Window,
};

use super::{
    channel::Channel,
    tioa::{EdgeTree, LocationTree, Traversal},
    tiots::{State, Transition, TIOTS},
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

    // FIXME: I think this should assign a readonly variable in the environment designated for the location.
    pub fn set_location(&mut self, locations: Vec<LocationTree>) {
        if self.states.len() != locations.len() {
            panic!()
        }
        for idx in 0..self.states.len() {
            self.states[idx].set_location(locations[idx].clone());
        }
    }
}

impl Index<usize> for HyperState {
    type Output = State;

    fn index(&self, index: usize) -> &Self::Output {
        &self.states[index]
    }
}

impl IndexMut<usize> for HyperState {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.states[index]
    }
}

#[derive(Clone, Debug)]
pub enum HyperTransition {
    Delay {
        state: HyperState,
    },

    Discrete {
        state: HyperState,
        traversals: Vec<Option<Traversal>>,
    },
}

impl HyperTransition {
    pub const fn delay(state: HyperState) -> Self {
        Self::Delay { state }
    }

    pub const fn discrete(state: HyperState, traversals: Vec<Option<Traversal>>) -> Self {
        Self::Discrete { state, traversals }
    }

    pub const fn state(&self) -> &HyperState {
        match self {
            HyperTransition::Delay { state } => state,
            HyperTransition::Discrete { state, .. } => state,
        }
    }

    pub fn transitions(transitions: Vec<Transition>) -> Result<Self, ()> {
        let (delays, discretes): (Vec<_>, Vec<_>) =
            transitions
                .into_iter()
                .partition_map(|transition| match transition {
                    Transition::Delay { state } => Left(state),
                    Transition::Discrete { state, traversal } => Right((state, Some(traversal))),
                });

        match (delays.is_empty(), discretes.is_empty()) {
            (false, true) => Ok(HyperTransition::delay(HyperState::new(delays))),
            (true, false) => {
                let (states, traversals): (Vec<_>, Vec<_>) = discretes.into_iter().unzip();
                Ok(HyperTransition::discrete(
                    HyperState::new(states),
                    traversals,
                ))
            }
            _ => Err(()),
        }
    }

    pub const fn is_delay(&self) -> bool {
        matches!(self, Self::Delay { .. })
    }

    pub const fn is_discrete(&self) -> bool {
        matches!(self, Self::Discrete { .. })
    }
}

impl From<HyperTransition> for Vec<Option<Transition>> {
    fn from(value: HyperTransition) -> Self {
        match value {
            HyperTransition::Delay { state } => state
                .into_iter()
                .map(|state| Some(Transition::delay(state)))
                .collect(),
            HyperTransition::Discrete { state, traversals } => state
                .into_iter()
                .zip(traversals.into_iter())
                .map(|(state, traversal)| match traversal {
                    Some(traversal) => Some(Transition::discrete(state, traversal)),
                    None => None,
                })
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
    fn discrete(
        &self,
        state: HyperState,
        traversals: Vec<Option<Traversal>>,
    ) -> Result<HyperState, ()>;
    fn is_valid(&self, state: &HyperState) -> Result<bool, ()>;
    fn is_enabled(&self, transition: HyperTransition) -> Result<bool, ()>;
    fn enabled(&self, state: &HyperState, channels: Vec<Option<Channel>>) -> Vec<HyperTransition>;
}

pub struct SystemOfSystems {
    systems: Vec<Box<dyn TIOTS>>,
}

impl SystemOfSystems {
    pub const fn new(systems: Vec<Box<dyn TIOTS>>) -> Self {
        Self { systems }
    }

    pub fn len(&self) -> usize {
        self.systems.len()
    }

    pub fn initial_state(&self) -> HyperState {
        let states = self
            .systems
            .iter()
            .map(|system| system.initial_state())
            .collect();
        HyperState::new(states)
    }

    pub fn guard(
        &self,
        state: HyperState,
        edges: Vec<Option<&EdgeTree>>,
    ) -> Result<HyperState, ()> {
        // Step 0: Copy the original state.
        let original = state.clone();

        // Step 1: Compute the zones which are enabled for the guards.
        let states: Vec<_> = self
            .systems
            .iter()
            .enumerate()
            .map(|(idx, system)| match edges[idx] {
                Some(edge) => system.guard(state[idx].clone(), edge),
                None => Ok(state[idx].clone()),
            })
            .collect();
        if states.iter().any(|state| state.is_err()) {
            return Err(());
        }
        let states: Vec<_> = states.into_iter().map(|state| state.unwrap()).collect();

        // Step 2: Compute the windows of the guard.
        let windows: Vec<_> = states
            .iter()
            .enumerate()
            .map(|(idx, current)| {
                match state[idx]
                    .zone()
                    .delay_enabled_window(current.zone()) {
                        Some(window) => Some(window),
                        None => None,
                    }
            })
            .collect();
        if windows.iter().any(|window| window.is_none()) {
            return Err(())
        }

        let windows = windows.into_iter().map(|window| window.unwrap()).collect();

        let common_window = match Window::intersections(windows) {
            Some(window) => window,
            None => return Err(()),
        };

        if common_window.is_zero() {
            return Err(())
        }

        println!("Common window: {}", common_window);

        // Step 3: Restrict discrete steps inside the common window.
        let clamped: Vec<_> = states
            .into_iter()
            .enumerate()
            .map(
                |(idx, state)| match original[idx].clamp_window(state, common_window) {
                    Ok(state) => state,
                    Err(_) => unreachable!(),
                },
            )
            .collect();

        Ok(HyperState::new(clamped))
    }

    pub fn update(
        &self,
        state: HyperState,
        edges: Vec<Option<&EdgeTree>>,
    ) -> Result<HyperState, ()> {
        let states: Vec<_> = self
            .systems
            .iter()
            .enumerate()
            .map(|(idx, system)| match edges[idx] {
                Some(edge) => system.update(state[idx].clone(), edge),
                None => Ok(state[idx].clone()),
            })
            .collect();
        if states.iter().any(|state| state.is_err()) {
            return Err(());
        }
        let states: Vec<_> = states.into_iter().map(|state| state.unwrap()).collect();

        Ok(HyperState::new(states))
    }

    /// Performs the state changes from the traversal and updates the states accordingly.
    pub fn discrete(
        &self,
        mut state: HyperState,
        traversals: Vec<Option<Traversal>>,
    ) -> Result<HyperState, ()> {
        let (edges, destinations): (Vec<_>, Vec<_>) = traversals
            .iter()
            .enumerate()
            .map(|(idx, traversal)| match traversal {
                Some(traversal) => (Some(traversal.edge()), traversal.destination().clone()),
                None => (None, state[idx].location().clone()),
            })
            .unzip();

        state = match self.guard(state, edges.clone()) {
            Ok(state) => state,
            Err(_) => return Err(()),
        };

        state = match self.update(state, edges) {
            Ok(state) => state,
            Err(_) => return Err(()),
        };

        state.set_location(destinations);

        Ok(state)
    }

    pub fn is_valid(&self, state: &HyperState) -> Result<bool, ()> {
        self.systems
            .iter()
            .enumerate()
            .try_fold(true, |_, (idx, system)| {
                match system.is_valid(&state[idx]) {
                    Ok(true) => Ok(true),
                    Ok(false) => Ok(false),
                    Err(_) => Err(()),
                }
            })
    }

    pub fn is_enabled(&self, transition: HyperTransition) -> Result<bool, ()> {
        if transition.is_delay() {
            return self.is_valid(transition.state());
        }

        let transitions: Vec<Option<Transition>> = transition.into();
        for (system, transition) in self.systems.iter().zip(transitions.into_iter()) {
            if let Some(transition) = transition {
                match system.is_enabled(&transition) {
                    Ok(true) => continue,
                    Ok(false) => return Ok(false),
                    Err(_) => return Err(()),
                }
            }
        }
        Ok(true)
    }

    pub fn enabled(
        &self,
        state: &HyperState,
        channels: Vec<Option<Channel>>,
    ) -> Vec<HyperTransition> {
        let mut hyper_transitions = Vec::new();

        for transitions in self
            .systems
            .iter()
            .enumerate()
            .map(|(idx, system)| match &channels[idx] {
                Some(channel) => system
                    .outgoing(&state[idx], channel)
                    .into_iter()
                    .map(Some)
                    .collect(),
                None => vec![None],
            })
            .multi_cartesian_product()
        {
            let (states, traversals): (Vec<_>, Vec<_>) = transitions
                .into_iter()
                .enumerate()
                .map(|(idx, transition)| match transition {
                    Some(transition) => match transition {
                        Transition::Delay { state } => (state, None),
                        Transition::Discrete { state, traversal } => (state, Some(traversal)),
                    },
                    None => (state[idx].clone(), None),
                })
                .unzip();

            let hyper_state = HyperState::new(states);
            let edges: Vec<_> = traversals
                .iter()
                .map(|traversal| match traversal {
                    Some(traversal) => Some(traversal.edge()),
                    None => None,
                })
                .collect();

            if let Ok(hyper_state) = self.guard(hyper_state, edges) {
                let hyper_transition = HyperTransition::discrete(hyper_state, traversals);
                hyper_transitions.push(hyper_transition);
            }
        }

        hyper_transitions
    }
}

impl Index<usize> for SystemOfSystems {
    type Output = Box<dyn TIOTS>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.systems[index]
    }
}
