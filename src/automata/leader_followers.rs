use crate::zones::delay::Delay;

use super::{
    channel::Channel,
    htiots::{HyperState, HyperTransition, SystemOfSystems, HTIOTS},
    tioa::Traversal,
    tiots::{State, TIOTS},
};

/// A system of systems where the delay requires all followers to be able to perform atleast the same delay
/// and they are clamped to perform that delay. Essentially, the followers has to delay the same as the leader
/// and if they are unable to delay that amount then there exists no delay.
pub struct LeaderFollowers {
    leader: usize,
    systems: SystemOfSystems,
}

impl LeaderFollowers {
    pub fn new(systems: Vec<Box<dyn TIOTS>>, leader: usize) -> Self {
        if leader >= systems.len() {
            panic!("the leader must be one of the systems")
        }

        Self {
            systems: SystemOfSystems::new(systems),
            leader,
        }
    }

    pub fn leader(&self) -> &dyn TIOTS {
        self.system_by_index(self.leader).unwrap()
    }

    pub fn system_by_index(&self, index: usize) -> Option<&dyn TIOTS> {
        if index < self.systems.len() {
            Some(&*self.systems[index])
        } else {
            None
        }
    }

    pub fn len(&self) -> usize {
        self.systems.len()
    }
}

impl HTIOTS for LeaderFollowers {
    fn initial_state(&self) -> HyperState {
        self.systems.initial_state()
    }

    fn delay(&self, state: HyperState) -> Result<HyperState, ()> {
        if state.len() != self.systems.len() {
            panic!("there must be a state for each system");
        }

        let mut extrapolations: Vec<State> = Vec::with_capacity(state.len());
        let mut delays: Vec<Option<Delay>> = vec![None; state.len()];
        for (system, before) in state.iter().enumerate() {
            // Step 1: Compute all the extrapolations.
            let after = match self.systems[system].delay(before.clone()) {
                Ok(after) => after,
                // Atleast one of the systems could not delay.
                Err(_) => return Err(()),
            };

            // Step 2: Compute the smallest delay possible.
            delays[system] = before.zone().min_delay(after.zone());

            extrapolations.push(after);
        }

        // No system performed any delay (Maybe they all got more restrictive).
        // Since no delay was performed we don't have to synchronise delays across systems.
        if delays.iter().all(|delay| delay.is_none()) {
            return Ok(HyperState::new(extrapolations));
        }

        // If the leader did not delay but instead got more permissive then it is the same as no delay.
        let mut leader_delay = delays[self.leader];
        if leader_delay.is_none() {
            leader_delay = Some(Delay::exact(0));
        }

        // Step 3: Check if any follower delay is less than the leader's.
        // If that is the case the follower is unable to follow the leader.
        if let Some(leader_delay) = leader_delay {
            // Looks for an example where a follower could not follow the leader.
            if delays.iter().any(|delay| match delay {
                Some(delay) => *delay < leader_delay,
                None => true,
            }) {
                return Err(());
            }
        }

        // Step 4: Clamp the delays of the extrapolated zones to not be more permissive than the global minimum.
        let mut synchronisations: Vec<State> = Vec::with_capacity(extrapolations.len());
        for (system, extrapolation) in extrapolations.into_iter().enumerate() {
            let synchronisation =
                match extrapolation.synchronise(&state[system], leader_delay.unwrap()) {
                    Ok(synchronisation) => synchronisation,
                    // Atleast one of the systems could not synchronise.
                    Err(_) => return Err(()),
                };

            synchronisations.push(synchronisation);
        }

        Ok(HyperState::new(synchronisations))
    }

    fn discrete(
        &self,
        state: HyperState,
        traversals: Vec<Option<Traversal>>,
    ) -> Result<HyperState, ()> {
        self.systems.discrete(state, traversals)
    }

    fn is_valid(&self, state: &HyperState) -> Result<bool, ()> {
        self.systems.is_valid(state)
    }

    fn is_enabled(&self, transition: HyperTransition) -> Result<bool, ()> {
        self.systems.is_enabled(transition)
    }

    fn enabled(&self, state: &HyperState, channels: Vec<Option<Channel>>) -> Vec<HyperTransition> {
        self.systems.enabled(state, channels)
    }
}

#[cfg(test)]
mod tests {
    // TODO: Test with more clocks.
    // TODO: Test with an initial state where the clocks are not all zero.
    // TODO: Check boundary cases where clocks have initial values and the delay has to be precise with strict and weak relations.

    use itertools::Itertools;

    use crate::{
        automata::{
            automaton::Automaton,
            automaton_builder::AutomatonBuilder,
            expressions::{Comparison, Expression},
            htiots::{HyperState, HTIOTS},
            partitioned_symbol_table::PartitionedSymbolTable,
            ta::TA,
        },
        zones::constraint::Relation,
    };

    use super::LeaderFollowers;

    /// Automaton with unbounded delay on initial location.
    fn new_automaton0(partition: u32, symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);

        // Local declarations:
        builder.add_clock(partition, "c0");
        let loc0_symbol = builder.add_symbol(partition, "0");

        // Build
        let loc0 = builder.add_location(loc0_symbol, None);
        builder.set_initial_location(loc0);

        builder.build().unwrap()
    }

    /// Automaton with bounded delay on initial location.
    fn new_automaton1(partition: u32, symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);

        // Local declarations:
        let clock = builder.add_clock(partition, "c0");
        let loc0_symbol = builder.add_symbol(partition, "0");

        // Build
        let clock_less_than_or_equal_20 =
            Expression::new_clock_constraint(clock.into(), Comparison::LessThanOrEqual, 20.into());

        let loc0 = builder.add_location(loc0_symbol, Some(clock_less_than_or_equal_20));
        builder.set_initial_location(loc0);

        builder.build().unwrap()
    }

    #[test]
    fn automaton0() {
        let mut symbols = PartitionedSymbolTable::new();
        let automaton = new_automaton0(0, &mut symbols);

        /*let contextual_automaton = automaton.in_context(&symbols);
        println!("{}", contextual_automaton.dot());*/

        assert_eq!(automaton.clock_count(), 1);
        assert_eq!(automaton.inputs().try_len().unwrap(), 0);
        assert_eq!(automaton.outputs().try_len().unwrap(), 0);
        assert_eq!(automaton.node_iter().try_len().unwrap(), 1);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 0);
    }

    #[test]
    fn automaton1() {
        let mut symbols = PartitionedSymbolTable::new();
        let automaton = new_automaton1(0, &mut symbols);

        /*let contextual_automaton = automaton.in_context(&symbols);
        println!("{}", contextual_automaton.dot());*/

        assert_eq!(automaton.clock_count(), 1);
        assert_eq!(automaton.inputs().try_len().unwrap(), 0);
        assert_eq!(automaton.outputs().try_len().unwrap(), 0);
        assert_eq!(automaton.node_iter().try_len().unwrap(), 1);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 0);
    }

    #[test]
    fn delay_leader_follower_indefinite() {
        let mut symbols = PartitionedSymbolTable::new();
        let leader_follower = LeaderFollowers::new(
            vec![
                Box::new(new_automaton0(0, &mut symbols)),
                Box::new(new_automaton0(1, &mut symbols)),
            ],
            0,
        );

        let mut state = leader_follower.initial_state();
        {
            let (leader_state, follower_state) = (&state[0], &state[1]);
            assert_eq!(
                "-x ≤ 0 ∧ x ≤ 0",
                leader_state.zone().fmt_conjunctions(&vec!["x"])
            );
            assert_eq!(
                "-x ≤ 0 ∧ x ≤ 0",
                follower_state.zone().fmt_conjunctions(&vec!["x"])
            );
        }

        state = leader_follower.delay(state).ok().unwrap();
        let (leader_state, follower_state) = (&state[0], &state[1]);
        assert_eq!("-x ≤ 0", leader_state.zone().fmt_conjunctions(&vec!["x"]));
        assert_eq!("-x ≤ 0", follower_state.zone().fmt_conjunctions(&vec!["x"]));
    }

    #[test]
    fn delay_leader_indefinite_follower_finite() {
        let mut symbols = PartitionedSymbolTable::new();
        let leader_follower = LeaderFollowers::new(
            vec![
                Box::new(new_automaton1(1, &mut symbols)),
                Box::new(new_automaton0(0, &mut symbols)),
            ],
            0,
        );

        let state = leader_follower.initial_state();
        {
            let (leader_state, follower_state) = (&state[0], &state[1]);
            assert_eq!(
                "-x ≤ 0 ∧ x ≤ 0",
                leader_state.zone().fmt_conjunctions(&vec!["x"])
            );
            assert_eq!(
                "-x ≤ 0 ∧ x ≤ 0",
                follower_state.zone().fmt_conjunctions(&vec!["x"])
            );
        }

        {
            let state = leader_follower.delay(state.clone()).ok().unwrap();
            let (leader_state, follower_state) = (&state[0], &state[1]);
            assert_eq!(
                "-x ≤ 0 ∧ x ≤ 20",
                leader_state.zone().fmt_conjunctions(&vec!["x"])
            );
            assert_eq!(
                "-x ≤ 0 ∧ x ≤ 20",
                follower_state.zone().fmt_conjunctions(&vec!["x"])
            );
        }

        {
            let states: Vec<_> = state.clone().into_iter().collect();
            let [mut leader_state, follower_state] = states.try_into().unwrap();
            leader_state = leader_state
                .tighten_lower(1, Relation::weak(-10))
                .ok()
                .unwrap();
            leader_state = leader_state
                .loosen_upper(1, Relation::weak(15))
                .ok()
                .unwrap();
            assert_eq!(
                "-x ≤ -10 ∧ x ≤ 15",
                leader_state.zone().fmt_conjunctions(&vec!["x"])
            );
            let state = HyperState::new(vec![leader_state, follower_state]);
            let state = leader_follower.delay(state.clone()).ok().unwrap();
            let (leader_state, follower_state) = (&state[0], &state[1]);
            assert_eq!(
                "-x ≤ -10 ∧ x ≤ 20",
                leader_state.zone().fmt_conjunctions(&vec!["x"])
            );
            assert_eq!(
                "-x ≤ 0 ∧ x ≤ 5",
                follower_state.zone().fmt_conjunctions(&vec!["x"])
            );
        }

        {
            let states: Vec<_> = state.clone().into_iter().collect();
            let [mut leader_state, follower_state] = states.try_into().unwrap();
            leader_state = leader_state
                .tighten_lower(1, Relation::weak(-10))
                .ok()
                .unwrap();
            leader_state = leader_state
                .loosen_upper(1, Relation::strict(15))
                .ok()
                .unwrap();
            assert_eq!(
                "-x ≤ -10 ∧ x < 15",
                leader_state.zone().fmt_conjunctions(&vec!["x"])
            );
            let state = HyperState::new(vec![leader_state, follower_state]);
            let state = leader_follower.delay(state.clone()).ok().unwrap();
            let (leader_state, follower_state) = (&state[0], &state[1]);
            assert_eq!(
                "-x ≤ -10 ∧ x ≤ 20",
                leader_state.zone().fmt_conjunctions(&vec!["x"])
            );
            assert_eq!(
                "-x ≤ 0 ∧ x ≤ 5",
                follower_state.zone().fmt_conjunctions(&vec!["x"])
            );
        }
    }

    #[test]
    fn delay_leader_finite_follower_indefinite() {
        let mut symbols = PartitionedSymbolTable::new();
        let leader_follower = LeaderFollowers::new(
            vec![
                Box::new(new_automaton0(0, &mut symbols)),
                Box::new(new_automaton1(1, &mut symbols)),
            ],
            0,
        );

        let state = leader_follower.initial_state();
        let (leader_state, follower_state) = (&state[0], &state[1]);
        assert_eq!(
            "-x ≤ 0 ∧ x ≤ 0",
            leader_state.zone().fmt_conjunctions(&vec!["x"])
        );
        assert_eq!(
            "-x ≤ 0 ∧ x ≤ 0",
            follower_state.zone().fmt_conjunctions(&vec!["x"])
        );

        assert!(leader_follower.delay(state).is_err());
    }
}
