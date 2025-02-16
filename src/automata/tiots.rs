use crate::{
    automata::extrapolator::Extrapolator,
    zones::{
        bounds::Bounds,
        constraint::{Clock, Relation},
        dbm::{Canonical, DBM},
    },
};

use super::{
    action::Action,
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

    pub const fn location(&self) -> &LocationTree {
        &self.location
    }

    pub fn set_location(&mut self, location: LocationTree) {
        self.location = location
    }

    pub const fn ref_zone(&self) -> &DBM<Canonical> {
        &self.zone
    }

    pub const fn mut_zone(&mut self) -> &mut DBM<Canonical> {
        &mut self.zone
    }

    pub fn extrapolate(mut self, bounds: Bounds) -> Result<Self, ()> {
        match self.zone.extrapolate(bounds) {
            Ok(zone) => {
                self.zone = zone;
                Ok(self)
            }
            Err(_) => Err(()),
        }
    }

    pub const fn ref_environemnt(&self) -> &Environment {
        &self.environment
    }

    pub fn decompose(self) -> (LocationTree, DBM<Canonical>, Environment) {
        (self.location, self.zone, self.environment)
    }
}

#[derive(Clone)]
pub enum Transition {
    Discrete { action: Action, destination: State },
    Delay { destination: State },
}

impl Transition {
    pub const fn new_discrete(action: Action, destination: State) -> Self {
        Self::Discrete {
            action,
            destination,
        }
    }

    pub const fn new_delay(destination: State) -> Self {
        Self::Delay { destination }
    }

    pub fn action(&self) -> Option<Action> {
        match self {
            Transition::Discrete { action, .. } => Some(*action),
            Transition::Delay { .. } => None,
        }
    }

    pub fn destination(&self) -> &State {
        match self {
            Transition::Discrete { destination, .. } => destination,
            Transition::Delay { destination } => destination,
        }
    }
}

pub trait TIOTS
where
    Self: TA + IOA,
{
    fn initial_state(&self) -> Result<State, ()>;
    fn delay(&self, state: State) -> Result<State, ()>;
    fn discrete(&self, state: State, traversal: &Traversal) -> Result<State, ()>;
    fn traversals(
        &self,
        state: &State,
        action: &Action,
    ) -> impl Iterator<Item = (State, Traversal)> + Clone;
}

impl<T: ?Sized + TIOA> TIOTS for T {
    fn initial_state(&self) -> Result<State, ()> {
        let location = self.initial_location();
        let zone = DBM::zero(self.clock_count());
        let mut environemnt = Environment::new();
        for clock in self.clocks() {
            environemnt.insert_clock(clock);
        }
        let state = State::new(location, zone, environemnt);
        self.delay(state)
    }

    /// Extrapolate the state zone on the location invariant.
    fn delay(&self, state: State) -> Result<State, ()> {
        let mut extrapolator = Extrapolator::new();
        let location = self.location(state.location()).unwrap();
        let bounds = extrapolator.bounds(
            Bounds::universe(self.clocks().len() as Clock),
            &state,
            &location.invariant(),
        );
        state.extrapolate(bounds)
    }

    /// Performs the discrete step over the edge updating the state with the traversal's edge update.
    fn discrete(&self, mut state: State, traversal: &Traversal) -> Result<State, ()> {
        // Interpreting the edge's update statement updates the clock values.
        // This can essentially reset, assign, or something else the clock values.
        // Closure is not applied on the state as the operations allowed on clocks
        // in the update statements will always produce a closed and non-empty state.
        let mut interpreter = Interpreter::new();
        state = interpreter.statement(state, traversal.edge().update());

        // Update the location of the state as the traversal has now completed.
        state.set_location(traversal.destination().clone());

        Ok(state)
    }

    /// Returns the states enabled by the edge and the traversal.
    fn traversals(
        &self,
        state: &State,
        action: &Action,
    ) -> impl Iterator<Item = (State, Traversal)> + Clone {
        self.outgoing_traversals(state.location(), *action)
            .into_iter()
            .flatten()
            .filter_map(move |traversal| {
                let mut extrapolator = Extrapolator::new();

                // Extrapolating the state on the guard's bounds means that the state becomming a
                // subset of the original state. This subset is the set allowed to traverse the edge.
                let edge_bounds =
                    extrapolator.bounds(Bounds::new(), &state, traversal.edge().guard());
                match state.clone().extrapolate(edge_bounds) {
                    Ok(extrapolation) => Some((extrapolation, traversal)),
                    Err(_) => None,
                }
            })
            .into_iter()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use petgraph::graph::DiGraph;
    use symbol_table::SymbolTable;

    use crate::automata::{
        action::Action,
        automaton::Automaton,
        edge::Edge,
        expressions::{Comparison, Expression},
        literal::Literal,
        location::Location,
        statements::Statement,
        tioa::{LocationTree, Traversal, TIOA},
        tiots::TIOTS,
    };

    #[test]
    fn test_automaton_1() {
        let symbols = SymbolTable::new();
        let loc_0 = symbols.intern("0");
        let loc_1 = symbols.intern("1");
        let moved_symbol = symbols.intern("moved");
        let clock = symbols.intern("clock");

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
            .outgoing_traversals(&LocationTree::Leaf(node_0), moved_action)
            .unwrap();
        assert_eq!(1, traversals_0.len());

        let traversals_1: Vec<Traversal> = automaton
            .outgoing_traversals(&LocationTree::Leaf(node_1), moved_action)
            .unwrap();
        assert_eq!(0, traversals_1.len());

        let initial_state = automaton.initial_state().unwrap();
        assert_eq!(
            "-x ≤ 0 ∧ x ≤ 5",
            initial_state.ref_zone().fmt_conjunctions(&vec!["x"])
        );

        let edge_01 = automaton.outgoing(node_0).collect::<Vec<_>>()[0].weight();
        let mut following = automaton
            .discrete(
                initial_state,
                &Traversal::new(edge_01.clone(), automaton.location_tree(node_1)),
            )
            .unwrap();
        following = automaton.delay(following).unwrap();
        assert_eq!(
            "-x ≤ 0 ∧ x < 10",
            following.ref_zone().fmt_conjunctions(&vec!["x"])
        );
    }
}
