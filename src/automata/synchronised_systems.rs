use crate::zones::constraint::Relation;

use super::{
    channel::Channel,
    htiots::{HyperState, HyperTransition, HTIOTS},
    tioa::Traversal,
    tiots::{State, Transition, TIOTS},
};

pub struct SynchronisedSystems {
    systems: Vec<Box<dyn TIOTS>>,
}

impl SynchronisedSystems {
    pub fn new(systems: Vec<Box<dyn TIOTS>>) -> Self {
        Self { systems }
    }
}

impl HTIOTS for SynchronisedSystems {
    fn initial_state(&self) -> HyperState {
        let states = self
            .systems
            .iter()
            .map(|system| system.initial_state())
            .collect();
        HyperState::new(states)
    }

    /// Computes the possible synchronised delay across multiple systems.
    ///
    /// This delay is the global allowed minimum for all systems and extrapolations are clamped to this value.
    ///
    /// _Example_:
    /// System `A` has two clocks `x` and `y`, and system `B` has the clock `u`. At both their own locations, the invariant
    /// allows the following:
    /// - `A` can delay `x` two time units and `y` three.
    /// - `B` restricts `u` one time unit.
    /// The global minimum delay is the smallest positive change in upper bounds between the original and extrapolated zones.
    /// - `A` local minimum delay is two time units.
    /// - `B` local minimum delay is None (as there are no positive change).
    /// Therefore, the global minimum delay is two time units.
    ///
    /// The synchronisation for each systems:
    /// - `A` for `x` it does nothing, but restricts the allowed delay og `y` by a single time unit.
    /// - `B` for `u` does not nothing as no delayed is performed.
    fn delay(&self, states: HyperState) -> Result<HyperState, ()> {
        if states.len() != self.systems.len() {
            panic!("there must be a state for each system");
        }

        let mut extrapolations: Vec<State> = Vec::with_capacity(states.len());
        let mut global_minimum_delay: Option<Relation> = None;
        for (system, state) in states.iter().enumerate() {
            // Step 1: Compute all the extrapolations.
            let extrapolation = match self.systems[system].delay(state.clone()) {
                Ok(extrapolation) => extrapolation,
                // Atleast one of the systems could not delay.
                Err(_) => return Err(()),
            };

            // Step 2: Compute the smallest delay possible.
            let local_minimum_delay = state.zone().min_delay(extrapolation.zone());
            if local_minimum_delay < global_minimum_delay {
                global_minimum_delay = local_minimum_delay;
            }

            extrapolations.push(extrapolation);
        }

        // No system performed any delay (Maybe they all got more restrictive).
        // Since no delay was performed we don't have to synchronise delays across systems.
        if global_minimum_delay.is_none() {
            return Ok(HyperState::new(extrapolations));
        }

        // Step 3: Clamp the delays of the extrapolated zones to not be more permissive than the global minimum.
        let mut synchronisations: Vec<State> = Vec::with_capacity(extrapolations.len());
        for (system, extrapolation) in extrapolations.into_iter().enumerate() {
            let synchronisation =
                match extrapolation.synchronise(&states[system], global_minimum_delay.unwrap()) {
                    Ok(synchronisation) => synchronisation,
                    // Atleast one of the systems could not synchronise.
                    Err(_) => return Err(()),
                };

            synchronisations.push(synchronisation);
        }

        Ok(HyperState::new(synchronisations))
    }

    /// Performs the state changes from the traversal and updates the states accordingly.
    fn discrete(&self, state: HyperState, traversals: Vec<Traversal>) -> Result<HyperState, ()> {
        let mut states = self
            .systems
            .iter()
            .enumerate()
            .map(|(idx, system)| system.discrete(state[idx].clone(), traversals[idx].clone()));
        if states.any(|state| state.is_err()) {
            return Err(());
        }
        Ok(HyperState::new(
            states.map(|state| state.unwrap()).collect(),
        ))
    }

    fn is_enabled(&self, transition: HyperTransition) -> Result<bool, ()> {
        let transitions: Vec<Transition> = transition.into();
        for (system, transition) in self.systems.iter().zip(transitions.iter()) {
            match system.is_enabled(transition) {
                Ok(true) => continue,
                Ok(false) => return Ok(false),
                Err(_) => return Err(()),
            }
        }
        Ok(true)
    }

    fn enabled(&self, state: &HyperState, channels: Vec<Channel>) -> Vec<HyperTransition> {
        todo!()
    }
}
