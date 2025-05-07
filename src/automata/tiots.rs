use crate::zones::{
    bounds::Bounds,
    constraint::{Clock, Limit, Relation, REFERENCE},
    dbm::{Canonical, DBM},
};

use super::{
    channel::Channel,
    environment::Environment,
    interpreter::Interpreter,
    ioa::IOA,
    ta::TA,
    tioa::{LocationTree, Traversal, TIOA},
};

#[derive(Clone, Debug)]
pub struct State {
    location: LocationTree,
    zone: DBM<Canonical>,
    environment: Environment,
}

impl State {
    pub const fn new(
        location: LocationTree,
        zone: DBM<Canonical>,
        environment: Environment,
    ) -> Self {
        Self {
            location,
            zone,
            environment,
        }
    }

    /// Returns the location the state is in.
    pub const fn location(&self) -> &LocationTree {
        &self.location
    }

    /// Returns the symbolic zone representation of the state.
    pub const fn zone(&self) -> &DBM<Canonical> {
        &self.zone
    }

    /// Returns the environment of the state storing all values of variables.
    pub const fn environment(&self) -> &Environment {
        &self.environment
    }

    /// Performs an un-constrained delay on the zone essentially allowing all clocks to be delayed indefinitely.
    pub fn delay(&mut self) {
        self.zone.up();
    }

    /// Returns the complete bounds of the state's zone.
    pub fn bounds(&mut self) -> Bounds {
        self.zone().into()
    }

    /// Clamps the delay between the original and extrapolated zone and is used to perform the same
    /// time delay across multiple systems essentially acting as a synchronisation of time.
    ///
    /// Q: Is this actually a new form of extrapolation?
    pub fn synchronise(mut self, before: &Self, max_delay: Relation) -> Result<Self, ()> {
        match before.zone().clamp_delay(self.zone, max_delay) {
            Ok(zone) => {
                self.zone = zone;
                Ok(self)
            }
            Err(_) => Err(()),
        }
    }

    /// Sets the clock to be assigned to its limit
    pub fn reset(&mut self, clock: Clock, limit: Limit) {
        self.zone.reset(clock, limit);
    }

    pub fn satisfies(&self, i: Clock, j: Clock, relation: Relation) -> bool {
        self.zone.satisfies(i, j, relation)
    }

    pub fn satisfies_upper(&self, clock: Clock, relation: Relation) -> bool {
        self.satisfies(clock, REFERENCE, relation)
    }

    pub fn satisfies_lower(&self, clock: Clock, relation: Relation) -> bool {
        self.satisfies(REFERENCE, clock, relation)
    }

    pub fn satisfies_limit(&self, clock: Clock, limit: Limit) -> bool {
        self.satisfies_lower(clock, Relation::weak(limit))
            && self.satisfies_upper(clock, Relation::weak(limit))
    }

    pub fn satisfies_difference_limit(&self, i: Clock, j: Clock, limit: Limit) -> bool {
        self.satisfies(i, j, Relation::weak(limit)) && self.satisfies(i, j, Relation::weak(limit))
    }

    pub fn set_limit(mut self, clock: Clock, limit: Limit) -> Result<Self, ()> {
        self = match self.tighten_lower(clock, Relation::weak(-limit)) {
            Ok(state) => state,
            Err(_) => return Err(()),
        };

        self = match self.tighten_upper(clock, Relation::weak(limit)) {
            Ok(state) => state,
            Err(_) => return Err(()),
        };

        Ok(self)
    }

    pub fn set_difference_limit(mut self, i: Clock, j: Clock, limit: Limit) -> Result<Self, ()> {
        self = match self.tighten(i, j, Relation::weak(limit)) {
            Ok(state) => state,
            Err(_) => return Err(()),
        };

        self = match self.tighten(i, j, Relation::weak(limit)) {
            Ok(state) => state,
            Err(_) => return Err(()),
        };

        Ok(self)
    }

    pub fn tighten(mut self, i: Clock, j: Clock, relation: Relation) -> Result<Self, ()> {
        match self.zone.tighten(i, j, relation) {
            Ok(zone) => {
                self.zone = zone;
                Ok(self)
            }
            Err(_) => return Err(()),
        }
    }

    pub fn tighten_upper(self, clock: Clock, relation: Relation) -> Result<Self, ()> {
        self.tighten(clock, REFERENCE, relation)
    }

    pub fn tighten_lower(self, clock: Clock, relation: Relation) -> Result<Self, ()> {
        self.tighten(REFERENCE, clock, relation)
    }

    pub fn loosen(mut self, i: Clock, j: Clock, relation: Relation) -> Result<Self, ()> {
        match self.zone.loosen(i, j, relation) {
            Ok(zone) => {
                self.zone = zone;
                Ok(self)
            }
            Err(_) => return Err(()),
        }
    }

    pub fn loosen_upper(self, clock: Clock, relation: Relation) -> Result<Self, ()> {
        self.loosen(clock, REFERENCE, relation)
    }

    pub fn loosen_lower(self, clock: Clock, relation: Relation) -> Result<Self, ()> {
        self.loosen(REFERENCE, clock, relation)
    }

    // FIXME: I think this should assign a readonly variable in the environment designated for the location.
    pub fn set_location(&mut self, location: LocationTree) {
        self.location = location
    }
}

/// Represents a transition in a timed automaton.
///
/// Transitions can either be:
/// - **Delay**: Represents the elapse of time without changing the location,
///   while staying within the bounds of the location's invariant.
/// - **Discrete**: Represents an immediate change, updating variables and potentially
///   moving to a different location, triggered by satisfying a guard condition.
#[derive(Clone, Debug)]
pub enum Transition {
    /// A delay transition, where only time progresses.
    Delay {
        /// The resulting state after the delay.
        state: State,
    },

    /// A discrete transition, involving a location change and variable updates.
    Discrete {
        /// The resulting state after the discrete transition.
        state: State,
        /// The traversal information associated with the transition (e.g., the edge taken).
        traversal: Traversal,
    },
}

impl Transition {
    /// Creates a new delay transition from the given state.
    pub const fn delay(state: State) -> Self {
        Self::Delay { state }
    }

    /// Creates a new discrete transition from the given state and traversal.
    pub const fn discrete(state: State, traversal: Traversal) -> Self {
        Self::Discrete { state, traversal }
    }

    /// Returns the `state` of the transition.
    pub const fn state(&self) -> &State {
        match &self {
            Transition::Delay { state } => state,
            Transition::Discrete { state, .. } => state,
        }
    }

    /// Returns `true` if the transition is a delay transition.
    pub const fn is_delay(&self) -> bool {
        matches!(self, Self::Delay { .. })
    }

    /// Returns `true` if the transition is a discrete transition.
    pub const fn is_discrete(&self) -> bool {
        matches!(self, Self::Discrete { .. })
    }
}

pub trait TIOTS
where
    Self: TA + IOA,
{
    /// Returns the initial state of the system.
    ///
    /// In the initial state, all clocks are set to zero, and variables are initialized
    /// according to the specification.
    fn initial_state(&self) -> State;

    /// Computes the next state by applying the given transition.
    ///
    /// Assumes that the transition is enabled. Returns an error if extrapolation fails,
    /// which can occur during a delay transition if the initial state's zone does not
    /// satisfy the location's invariant.
    ///
    /// In timed automata, transitions are classified as:
    /// - **Delay Transition**: Extends the zone as far as permitted by the location's invariant.
    /// - **Discrete Transition**: Updates variables and moves the state to a new location.
    ///
    /// Returns `Ok(State)` if the transition succeeds, or `Err(())` if it fails.
    fn transition(&self, transition: Transition) -> Result<State, ()> {
        match transition {
            Transition::Delay { state } => self.delay(state),
            Transition::Discrete { state, traversal } => self.discrete(state, traversal),
        }
    }

    /// Applies a delay transition to the given `State`.
    ///
    /// - Advances time in the system while ensuring location invariants are maintained.
    /// - Internally calls `transition` with a `Delay` transition.
    ///
    /// # Parameters
    /// - `state`: The current `State` before the delay.
    ///
    /// # Returns
    /// - `Ok(State)`: The new state after time has been allowed to progress.
    /// - `Err(())`: If the delay is not possible due to invariant violations or transition failure.
    fn delay(&self, state: State) -> Result<State, ()>;

    /// Applies a discrete transition to the given `State` using the provided `Traversal`.
    ///
    /// - Updates the system state based on the traversal's update statements.
    /// - Changes the location to the traversal's destination.
    /// - Internally calls `transition` with a `Discrete` transition.
    ///
    /// # Parameters
    /// - `state`: The current `State` before the discrete move.
    /// - `traversal`: The `Traversal` representing the edge and destination location for the transition.
    ///
    /// # Returns
    /// - `Ok(State)`: The new state after applying the discrete transition.
    /// - `Err(())`: If the discrete transition is not possible due to guard or invariant violations, or transition failure.
    fn discrete(&self, state: State, traversal: Traversal) -> Result<State, ()>;

    /// Checks if the state is valid in the system.
    ///
    /// Ie. Verifies whether the current state satisfies the invariant of the current location.
    /// If the location is not in the system then an error is returned.
    fn is_valid(&self, state: &State) -> Result<bool, ()>;

    /// Checks whether the given transition is enabled from the current state.
    ///
    /// Returns `Ok(())` if the transition is enabled, or `Err(())` otherwise.
    fn is_enabled(&self, transition: &Transition) -> Result<bool, ()>;

    /// Returns a list of all transitions enabled from the given state.
    ///
    /// This method takes into account both the current system state and the channel
    /// synchronization context to determine which transitions are available.
    ///
    /// # Parameters
    /// - `state`: The current state from which transitions are evaluated.
    /// - `channel`: The channel context used for synchronization between components.
    ///
    /// # Returns
    /// A vector containing all enabled transitions.
    fn enabled(&self, state: &State, channel: &Channel) -> Vec<Transition>;
}

impl<T: ?Sized + TIOA> TIOTS for T {
    /// Returns the initial `State` of the system.
    ///
    /// - Sets the location to the automaton's initial location.
    /// - Initializes a clock environment with all clocks declared in the model.
    /// - Initializes the zone to represent all clocks starting at zero.
    ///
    /// # Returns
    /// A `State` representing the initial configuration of the automaton.
    fn initial_state(&self) -> State {
        let location = self.initial_location();
        let zone = DBM::zero(self.clock_count());
        let mut environment = Environment::new();
        for clock in self.clocks() {
            environment.insert_clock(clock);
        }
        State::new(location, zone, environment)
    }

    fn delay(&self, mut state: State) -> Result<State, ()> {
        let location = match self.location(state.location()) {
            Ok(location) => location,
            Err(_) => return Err(()),
        };

        state.delay();

        let mut interpreter = Interpreter::new();
        state = match interpreter.constrain(state, &location.invariant()) {
            Ok(state) => state,
            Err(_) => return Err(()),
        };

        // TODO: Perform extrapolation to ensure clocks do not grow beyond the maximal constants in the model.
        // However, maybe extrapolation breaks the hyper system.

        Ok(state)
    }

    fn discrete(&self, mut state: State, traversal: Traversal) -> Result<State, ()> {
        let edge = match self.edge(traversal.edge()) {
            Ok(edge) => edge,
            Err(_) => return Err(()),
        };

        let mut interpreter = Interpreter::new();
        state = match interpreter.statement(state, edge.update()) {
            Ok(state) => state,
            Err(_) => return Err(()),
        };
        state.set_location(traversal.destination().clone());

        Ok(state)
    }

    fn is_valid(&self, state: &State) -> Result<bool, ()> {
        let location = match self.location(state.location()) {
            Ok(location) => location,
            Err(_) => return Err(()),
        };

        let mut interpreter = Interpreter::new();

        match interpreter.satisfies(state, &location.invariant()) {
            Ok(satisfied) => Ok(satisfied),
            Err(_) => return Err(()),
        }
    }

    /// Checks whether a given `Transition` is currently enabled from the starting `State`.
    ///
    /// - For a `Delay` transition: It checks if the state is valid.
    ///   - Verifies whether the current state satisfies the invariant of the current location.
    ///
    /// - For a `Discrete` transition:
    ///   - Checks that the guard condition of the edge is satisfied.
    ///   - Applies the edge's update.
    ///   - Verifies that the destination location's invariant holds after the update.
    ///
    /// # Parameters
    /// - `transition`: A reference to the `Transition` to check.
    ///
    /// # Returns
    /// - `Ok(true)`: If the transition is enabled.
    /// - `Ok(false)`: If the transition is disabled.
    /// - `Err(())`: If an error occurs during guard evaluation, statement execution, or invariant checking.
    fn is_enabled(&self, transition: &Transition) -> Result<bool, ()> {
        // All transitions must start in a valid state.
        match self.is_valid(transition.state()) {
            Ok(false) => return Ok(false),
            Err(_) => return Err(()),
            _ => {}
        }

        // Only the discrete transition traverse a potentially guarded edge to a location.
        if let Transition::Discrete {
            ref state,
            traversal,
        } = transition
        {
            let mut interpreter = Interpreter::new();

            let edge = match self.edge(traversal.edge()) {
                Ok(edge) => edge,
                Err(_) => return Err(()),
            };

            // Checks if the edge's guard is enabled.
            let satisfied = match interpreter.satisfies(&state, edge.guard()) {
                Ok(satisfied) => satisfied,
                Err(_) => return Err(()),
            };

            if !satisfied {
                return Ok(false);
            }

            // Performs the update on the state.
            let state = match interpreter.statement(state.clone(), &edge.update()) {
                Ok(state) => state,
                Err(_) => return Err(()),
            };

            // Checks if the updated state satisfies the location's invariant.
            return self.is_enabled(&Transition::delay(state));
        }

        Ok(true)
    }

    /// Computes all enabled discrete transitions from a given `State` on a specific `Channel`.
    ///
    /// - Retrieves all traversals (edges) from the current location for the given channel.
    /// - Filters traversals by checking whether each discrete transition is enabled using `is_enabled`.
    ///
    /// # Parameters
    /// - `state`: The current `State`.
    /// - `channel`: The `Channel` on which outgoing transitions are considered.
    ///
    /// # Returns
    /// A `Vec<Transition>` containing all enabled discrete transitions for the specified channel.
    fn enabled(&self, state: &State, channel: &Channel) -> Vec<Transition> {
        self.outgoing_traversals(state.location(), *channel)
            .into_iter()
            .flatten()
            .filter_map(move |traversal| {
                let transition = Transition::discrete(state.clone(), traversal);
                match self.is_enabled(&transition) {
                    Ok(true) => Some(transition),
                    Ok(false) | Err(_) => None,
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use petgraph::{graph::DiGraph, visit::EdgeRef};

    use crate::automata::{
        action::Action,
        automaton::Automaton,
        edge::Edge,
        expressions::{Comparison, Expression},
        literal::Literal,
        location::Location,
        partitioned_symbol_table::PartitionedSymbolTable,
        statements::Statement,
        tioa::{EdgeTree, LocationTree, Traversal, TIOA},
        tiots::TIOTS,
    };

    #[test]
    fn test_automaton_1() {
        let symbols = PartitionedSymbolTable::new();
        let loc_0 = symbols.intern(0, "0");
        let loc_1 = symbols.intern(0, "1");
        let moved_symbol = symbols.intern(0, "moved");
        let clock = symbols.intern(0, "clock");

        let mut graph = DiGraph::new();
        let node_0 = graph.add_node(Location::new(
            loc_0,
            Expression::new_clock_constraint(
                Literal::new_identifier(clock).into(),
                Comparison::LessThanOrEqual,
                Literal::new_i16(5).into(),
            ),
        ));
        let node_1 = graph.add_node(Location::new(
            loc_1,
            Expression::new_clock_constraint(
                Literal::new_identifier(clock).into(),
                Comparison::LessThan,
                Literal::new_i16(10).into(),
            ),
        ));

        let moved_action = Action::new(moved_symbol);

        graph.add_edge(
            node_0,
            node_1,
            Edge::new_output(
                moved_action,
                Expression::new_clock_constraint(
                    Literal::new_identifier(clock).into(),
                    Comparison::GreaterThan,
                    Literal::new_i16(2).into(),
                ),
                Statement::empty(),
            ),
        );

        let automaton =
            Automaton::new(node_0, graph, HashSet::from_iter(vec![clock].into_iter())).unwrap();

        assert_eq!(1, automaton.out_degree(node_0));
        assert_eq!(0, automaton.in_degree(node_0));
        assert_eq!(0, automaton.out_degree(node_1));
        assert_eq!(1, automaton.in_degree(node_1));

        let traversals_0: Vec<Traversal> = automaton
            .outgoing_traversals(&LocationTree::Leaf(node_0), moved_action.output())
            .unwrap();
        assert_eq!(1, traversals_0.len());

        let traversals_1: Vec<Traversal> = automaton
            .outgoing_traversals(&LocationTree::Leaf(node_1), moved_action.output())
            .unwrap();
        assert_eq!(0, traversals_1.len());

        let mut initial_state = automaton.initial_state();
        initial_state = automaton.delay(initial_state).unwrap();
        assert_eq!(
            "-x ≤ 0 ∧ x ≤ 5",
            initial_state.zone().fmt_conjunctions(&vec!["x"])
        );

        let edge_01 = automaton.outgoing(node_0).collect::<Vec<_>>()[0].id();
        let mut following = automaton
            .discrete(
                initial_state,
                Traversal::step(EdgeTree::leaf(edge_01), LocationTree::new_leaf(node_1)),
            )
            .unwrap();
        following = automaton.delay(following).unwrap();
        assert_eq!(
            "-x ≤ 0 ∧ x < 10",
            following.zone().fmt_conjunctions(&vec!["x"])
        );
    }
}
