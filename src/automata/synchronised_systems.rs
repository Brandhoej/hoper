use super::{
    tioa::Traversal,
    tiots::{State, TIOTS},
};

/// Systems of multiple TIOTS
pub trait STIOTS {
    fn initial_state(&self) -> Result<Vec<State>, ()>;
    fn delay(&self, states: Vec<State>) -> Result<Vec<State>, ()>;
    fn traverse(&self, states: Vec<State>, traversals: Vec<Traversal>) -> Vec<Result<State, ()>>;
}

pub struct SynchronisedSystems {
    systems: Vec<Box<dyn TIOTS>>,
}

impl SynchronisedSystems {
    pub fn new(systems: Vec<Box<dyn TIOTS>>) -> Self {
        Self { systems }
    }
}

impl STIOTS for SynchronisedSystems {
    fn initial_state(&self) -> Result<Vec<State>, ()> {
        self.delay(
            self.systems
                .iter()
                .map(|system| system.initial_state())
                .collect(),
        )
    }

    fn delay(&self, before: Vec<State>) -> Result<Vec<State>, ()> {
        // Step 1: Delay for all systems.
        let extrapolations: Vec<_> = before
            .iter()
            .enumerate()
            .map(|(idx, state)| self.systems[idx].delay(state.clone()))
            .collect();

        // Atleast one of the systems could not delay.
        if extrapolations.iter().any(|result| result.is_err()) {
            return Err(());
        }

        // We have checked that all returns an answer and therefore, we know
        // all results are OK and we can then construct this new vector.
        let after: Vec<_> = extrapolations
            .into_iter()
            .map(|extrapolation| extrapolation.unwrap())
            .collect();

        // Step 2: Compute the required delays across all delays.
        let minimum_delays: Vec<_> = before
            .into_iter()
            .enumerate()
            .map(|(idx, before)| {
                let before_zone = before.ref_zone();
                let after_zone = after[idx].ref_zone();
                return before_zone.min_delay(after_zone);
            })
            .collect();

        // Step 3: Find the synchronous delay which is the greatest delay which can occur across all systems.
        let global_minimum_delay = minimum_delays.iter().min().unwrap();

        // Step 4: Compute the adjustments to the upper-bounds of the clocks.
        let adjustments: Vec<_> = minimum_delays
            .iter()
            .map(|local_minimum_delay| *local_minimum_delay - *global_minimum_delay)
            .collect();

        // Step 5: Clamp delays across all zones which acts as the synchronisation.
        let adjusted: Vec<_> = after
            .into_iter()
            .enumerate()
            .map(|(idx, state)| state.delay(-adjustments[idx]))
            .collect();

        // Check if any zone could not be adjusted (synchronised).
        if adjusted.iter().any(|state| state.is_err()) {
            return Err(());
        }

        // All could be adjusted and we just return the collection of states.
        Ok(adjusted
            .into_iter()
            .map(|state| state.ok().unwrap())
            .collect())
    }

    fn traverse(&self, states: Vec<State>, traversals: Vec<Traversal>) -> Vec<Result<State, ()>> {
        self.systems
            .iter()
            .enumerate()
            .map(|(idx, system)| system.traverse(states[idx].clone(), &traversals[idx]))
            .collect()
    }
}
