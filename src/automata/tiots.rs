use crate::{
    automata::extrapolator::Extrapolator,
    zones::{
        bounds::Bounds,
        constraint::Clock,
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
    fn update(&self, state: State, traversal: &Traversal) -> Result<State, ()>;
    fn guard(&self, state: State, traversal: &Traversal) -> Result<State, ()>;
    fn guards(
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

    fn update(&self, mut state: State, traversal: &Traversal) -> Result<State, ()> {
        if traversal.edge().is_identity() {
            return Ok(state);
        }

        let edge = self.edge(traversal.edge()).unwrap();

        let mut interpreter = Interpreter::new();
        state = interpreter.statement(state, edge.update());
        state.set_location(traversal.destination().clone());

        Ok(state)
    }

    fn guard(&self, state: State, traversal: &Traversal) -> Result<State, ()> {
        if traversal.edge().is_identity() {
            return Ok(state);
        }

        let edge = self.edge(traversal.edge()).unwrap();

        let mut extrapolator = Extrapolator::new();
        let edge_bounds = extrapolator.bounds(Bounds::new(), &state, edge.guard());

        match state.extrapolate(edge_bounds) {
            Ok(extrapolation) => Ok(extrapolation),
            Err(_) => return Err(()),
        }
    }

    /// Returns the states enabled by the edge and the traversal.
    fn guards(
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
                let edge = self.edge(traversal.edge());
                let edge_bounds = extrapolator.bounds(Bounds::new(), &state, edge.unwrap().guard());
                return match state.clone().extrapolate(edge_bounds) {
                    Ok(extrapolation) => Some((extrapolation, traversal)),
                    Err(_) => None,
                };
            })
            .into_iter()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use itertools::Itertools;
    use petgraph::{graph::DiGraph, visit::EdgeRef};

    use crate::{
        automata::{
            action::Action,
            automaton::Automaton,
            automaton_builder::AutomatonBuilder,
            edge::Edge,
            environment::Environment,
            expressions::{Comparison, Expression},
            literal::Literal,
            location::Location,
            partitioned_symbol_table::PartitionedSymbolTable,
            statements::Statement,
            tioa::{EdgeTree, LocationTree, Traversal, TIOA},
            tiots::TIOTS,
        },
        zones::{
            constraint::{Relation, REFERENCE},
            dbm::DBM,
        },
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

        let edge_01 = automaton.outgoing(node_0).collect::<Vec<_>>()[0].id();
        let mut following = automaton
            .update(
                initial_state,
                &Traversal::step(EdgeTree::leaf(edge_01), LocationTree::new_leaf(node_1)),
            )
            .unwrap();
        following = automaton.delay(following).unwrap();
        assert_eq!(
            "-x ≤ 0 ∧ x < 10",
            following.ref_zone().fmt_conjunctions(&vec!["x"])
        );
    }

    #[test]
    fn test_automaton_2() {
        let symbols = &mut PartitionedSymbolTable::new();
        let mut builder = AutomatonBuilder::new(symbols);

        let x = builder.add_clock(0, "x");

        let loc0_index = builder.add_location_with_name(0, "loc0");
        let loc1_index = builder.add_location(
            0,
            "loc1",
            Expression::new_clock_constraint(x.into(), Comparison::LessThanOrEqual, 8.into()),
        );
        let loc2_index = builder.add_location_with_name(0, "loc2");
        let loc3_index = builder.add_location_with_name(0, "loc3");

        builder.set_initial_location(loc0_index);

        let e01_index = builder.add_edge_input(
            0,
            loc0_index,
            loc1_index,
            "action",
            Some(Expression::new_clock_constraint(
                x.into(),
                Comparison::LessThanOrEqual,
                15.into(),
            )),
            Some(Statement::reset(x, 0)),
        );
        let e12_index = builder.add_edge_input(
            0,
            loc1_index,
            loc2_index,
            "action",
            Some(Expression::new_clock_constraint(
                x.into(),
                Comparison::GreaterThanOrEqual,
                4.into(),
            )),
            Some(Statement::reset(x, 0)),
        );
        let e23_index = builder.add_edge_input(
            0,
            loc3_index,
            loc3_index,
            "action",
            Some(Expression::new_clock_constraint(
                x.into(),
                Comparison::GreaterThan,
                15.into(),
            )),
            None,
        );

        let automaton = builder.build().unwrap();
        assert_eq!(automaton.inputs().try_len().unwrap(), 1);
        assert_eq!(automaton.outputs().try_len().unwrap(), 0);
        assert_eq!(automaton.node_iter().try_len().unwrap(), 4);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 3);

        let e01 = EdgeTree::leaf(e01_index);
        let e12 = EdgeTree::leaf(e12_index);
        let e23 = EdgeTree::leaf(e23_index);

        let loc1 = LocationTree::new_leaf(loc1_index);
        let loc2 = LocationTree::new_leaf(loc2_index);
        let loc3 = LocationTree::new_leaf(loc3_index);

        let mut state = automaton.initial_state().unwrap();
        assert_eq!("-x ≤ 0", state.ref_zone().fmt_conjunctions(&vec!["x"]));

        state = automaton
            .update(state, &Traversal::step(e01, loc1))
            .unwrap();
        assert_eq!(
            "-x ≤ 0 ∧ x ≤ 0",
            state.ref_zone().fmt_conjunctions(&vec!["x"])
        );

        state = automaton.delay(state).unwrap();
        assert_eq!(
            "-x ≤ 0 ∧ x ≤ 8",
            state.ref_zone().fmt_conjunctions(&vec!["x"])
        );

        state = automaton
            .update(state, &Traversal::step(e12, loc2))
            .unwrap();
        assert_eq!(
            "-x ≤ 0 ∧ x ≤ 0",
            state.ref_zone().fmt_conjunctions(&vec!["x"])
        );

        state = automaton.delay(state).unwrap();
        assert_eq!("-x ≤ 0", state.ref_zone().fmt_conjunctions(&vec!["x"]));

        state = automaton
            .update(state, &Traversal::step(e23, loc3))
            .unwrap();
        assert_eq!("-x ≤ 0", state.ref_zone().fmt_conjunctions(&vec!["x"]));
    }

    #[test]
    fn test_automaton_3() {
        let symbols = &mut PartitionedSymbolTable::new();
        let mut builder = AutomatonBuilder::new(symbols);

        let x_id = builder.add_clock(0, "x");
        let y_id = builder.add_clock(0, "y");

        let loc0 = builder.add_location_with_name(0, "loc0");
        let loc1 = builder.add_location_with_name(0, "loc1");
        let loc2 = builder.add_location_with_name(0, "loc2");
        let loc3 = builder.add_location_with_name(0, "loc3");
        assert!(loc0 != loc1 && loc1 != loc2 && loc2 != loc3);

        builder.set_initial_location(loc0);

        // if -x ≤ 0 ∧ x - y ≤ -6 ∧ -y ≤ -6 ∧ y - x < 23
        let guard_0 = Expression::conjunctions(vec![
            Expression::new_diagonal_clock_constraint(
                x_id.into(),
                y_id.into(),
                Comparison::GreaterThanOrEqual,
                6.into(),
            ),
            Expression::new_diagonal_clock_constraint(
                y_id.into(),
                x_id.into(),
                Comparison::LessThan,
                23.into(),
            ),
            Expression::new_clock_constraint(y_id.into(), Comparison::GreaterThanOrEqual, 6.into()),
        ]); 
        let e01 = builder.add_edge_input(0, loc0, loc1, "action", Some(guard_0), None);

        // if y ≥ 2 ∧ x ≤ 15 then x := 0
        let guard_1 = Expression::conjunctions(vec![
            Expression::new_clock_constraint(y_id.into(), Comparison::GreaterThanOrEqual, 2.into()),
            Expression::new_clock_constraint(x_id.into(), Comparison::LessThanOrEqual, 15.into()),
        ]);
        let e12 = builder.add_edge_input(0, loc1, loc2, "action", Some(guard_1), None);

        // y ≥ 2 ∧ x > 15
        let guard_2 = Expression::conjunctions(vec![
            Expression::new_clock_constraint(y_id.into(), Comparison::GreaterThanOrEqual, 2.into()),
            Expression::new_clock_constraint(x_id.into(), Comparison::GreaterThan, 15.into()),
        ]);
        let e13 = builder.add_edge_input(0, loc1, loc3, "action", Some(guard_2), None);

        let automaton = builder.build().unwrap();
        assert_eq!(automaton.inputs().try_len().unwrap(), 1);
        assert_eq!(automaton.outputs().try_len().unwrap(), 0);
        assert_eq!(automaton.node_iter().try_len().unwrap(), 4);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 3);

        let mut state = automaton.initial_state().unwrap();
        let x = state.environment.get_clock(x_id).unwrap();
        let y = state.environment.get_clock(y_id).unwrap();

        let mut labels = vec!["", ""];
        labels[(x - 1) as usize] = "x";
        labels[(y - 1) as usize] = "y";

        let conjunctions = state.ref_zone().fmt_conjunctions(&labels);
        assert!(conjunctions.contains("-x ≤ 0"));
        assert!(conjunctions.contains("x - y ≤ 0"));
        assert!(conjunctions.contains("-y ≤ 0"));
        assert!(conjunctions.contains("y - x ≤ 0"));

        // Makes the initial state the universe.
        state.mut_zone().free(x);
        state.mut_zone().free(y);

        let conjunctions = state.ref_zone().fmt_conjunctions(&labels);
        assert!(conjunctions.contains("-x ≤ 0"));
        assert!(conjunctions.contains("-y ≤ 0"));

        state = automaton
            .guard(state, &Traversal::step(e01.into(), loc1.into()))
            .unwrap();

        // -y ≤ -6 ∧ y - x < 23 ∧ -x ≤ 0 ∧ x - y ≤ -6
        let conjunctions = state.ref_zone().fmt_conjunctions(&labels);
        assert!(conjunctions.contains("-x ≤ 0"));
        assert!(conjunctions.contains("x - y ≤ -6"));
        assert!(conjunctions.contains("-y ≤ -6"));
        assert!(conjunctions.contains("y - x < 23"));

        let state_0 = automaton
            .guard(state.clone(), &Traversal::step(e12.into(), loc2.into()))
            .unwrap();

        // -y ≤ -6 ∧ y < 38 ∧ y - x < 23 ∧ -x ≤ 0 ∧ x ≤ 15 ∧ x - y ≤ -6
        let conjunctions = state_0.ref_zone().fmt_conjunctions(&labels);
        assert!(conjunctions.contains("-y ≤ -6"));
        assert!(conjunctions.contains("y < 38"));
        assert!(conjunctions.contains("y - x < 23"));
        assert!(conjunctions.contains("-x ≤ 0"));
        assert!(conjunctions.contains("x ≤ 15"));
        assert!(conjunctions.contains("x - y ≤ -6"));

        let state_1 = automaton
            .guard(state.clone(), &Traversal::step(e13.into(), loc3.into()))
            .unwrap();

        // -x < -15 ∧ x - y ≤ -6 ∧ -y < -21 ∧ y - x < 23
        let conjunctions = state_1.ref_zone().fmt_conjunctions(&labels);
        assert!(conjunctions.contains("-x < -15"));
        assert!(conjunctions.contains("x - y ≤ -6"));
        assert!(conjunctions.contains("-y < -21"));
        assert!(conjunctions.contains("y - x < 23"));

        assert_eq!("[0, ∞]", state.ref_zone().interval().to_string());
        assert_eq!("[0, 15]", state_0.ref_zone().interval().to_string());
        assert_eq!("(15, ∞]", state_1.ref_zone().interval().to_string());
        
        let delyed_by_0 = state.ref_zone().delayed_by(state_0.ref_zone());
        assert_eq!("[0, 15]", delyed_by_0.to_string());

        let delyed_by_1 = state.ref_zone().delayed_by(state_1.ref_zone());
        assert_eq!("(15, ∞]", delyed_by_1.to_string());

        assert!(delyed_by_0.intersection(&delyed_by_1).is_none());
    }

    #[test]
    fn test_automaton_4() {
        // This is like automaton_3 but where the guards overlap.

        let symbols = &mut PartitionedSymbolTable::new();
        let mut builder = AutomatonBuilder::new(symbols);

        let x_id = builder.add_clock(0, "x");
        let y_id = builder.add_clock(0, "y");

        let loc0 = builder.add_location_with_name(0, "loc0");
        let loc1 = builder.add_location_with_name(0, "loc1");
        let loc2 = builder.add_location_with_name(0, "loc2");
        let loc3 = builder.add_location_with_name(0, "loc3");
        assert!(loc0 != loc1 && loc1 != loc2 && loc2 != loc3);

        builder.set_initial_location(loc0);

        // if -x ≤ 0 ∧ x - y ≤ -6 ∧ -y ≤ -6 ∧ y - x < 23
        let guard_0 = Expression::conjunctions(vec![
            Expression::new_diagonal_clock_constraint(
                x_id.into(),
                y_id.into(),
                Comparison::GreaterThanOrEqual,
                6.into(),
            ),
            Expression::new_diagonal_clock_constraint(
                y_id.into(),
                x_id.into(),
                Comparison::LessThan,
                23.into(),
            ),
            Expression::new_clock_constraint(y_id.into(), Comparison::GreaterThanOrEqual, 6.into()),
        ]); 
        let e01 = builder.add_edge_input(0, loc0, loc1, "action", Some(guard_0), None);

        // if y ≥ 2 ∧ x ≤ 15 then x := 0
        let guard_1 = Expression::conjunctions(vec![
            Expression::new_clock_constraint(y_id.into(), Comparison::GreaterThanOrEqual, 2.into()),
            Expression::new_clock_constraint(x_id.into(), Comparison::LessThanOrEqual, 15.into()),
        ]);
        let e12 = builder.add_edge_input(0, loc1, loc2, "action", Some(guard_1), None);

        // y ≥ 2 ∧ x > 10
        let guard_2 = Expression::conjunctions(vec![
            Expression::new_clock_constraint(y_id.into(), Comparison::GreaterThanOrEqual, 2.into()),
            Expression::new_clock_constraint(x_id.into(), Comparison::GreaterThan, 10.into()),
        ]);
        let e13 = builder.add_edge_input(0, loc1, loc3, "action", Some(guard_2), None);

        let automaton = builder.build().unwrap();
        assert_eq!(automaton.inputs().try_len().unwrap(), 1);
        assert_eq!(automaton.outputs().try_len().unwrap(), 0);
        assert_eq!(automaton.node_iter().try_len().unwrap(), 4);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 3);

        let mut state = automaton.initial_state().unwrap();
        let x = state.environment.get_clock(x_id).unwrap();
        let y = state.environment.get_clock(y_id).unwrap();

        let mut labels = vec!["", ""];
        labels[(x - 1) as usize] = "x";
        labels[(y - 1) as usize] = "y";

        let conjunctions = state.ref_zone().fmt_conjunctions(&labels);
        assert!(conjunctions.contains("-x ≤ 0"));
        assert!(conjunctions.contains("x - y ≤ 0"));
        assert!(conjunctions.contains("-y ≤ 0"));
        assert!(conjunctions.contains("y - x ≤ 0"));

        // Makes the initial state the universe.
        state.mut_zone().free(x);
        state.mut_zone().free(y);

        let conjunctions = state.ref_zone().fmt_conjunctions(&labels);
        assert!(conjunctions.contains("-x ≤ 0"));
        assert!(conjunctions.contains("-y ≤ 0"));

        state = automaton
            .guard(state, &Traversal::step(e01.into(), loc1.into()))
            .unwrap();

        // -y ≤ -6 ∧ y - x < 23 ∧ -x ≤ 0 ∧ x - y ≤ -6
        let conjunctions = state.ref_zone().fmt_conjunctions(&labels);
        assert!(conjunctions.contains("-x ≤ 0"));
        assert!(conjunctions.contains("x - y ≤ -6"));
        assert!(conjunctions.contains("-y ≤ -6"));
        assert!(conjunctions.contains("y - x < 23"));

        let state_0 = automaton
            .guard(state.clone(), &Traversal::step(e12.into(), loc2.into()))
            .unwrap();

        // -y ≤ -6 ∧ y < 38 ∧ y - x < 23 ∧ -x ≤ 0 ∧ x ≤ 15 ∧ x - y ≤ -6
        let conjunctions = state_0.ref_zone().fmt_conjunctions(&labels);
        assert!(conjunctions.contains("-y ≤ -6"));
        assert!(conjunctions.contains("y < 38"));
        assert!(conjunctions.contains("y - x < 23"));
        assert!(conjunctions.contains("-x ≤ 0"));
        assert!(conjunctions.contains("x ≤ 15"));
        assert!(conjunctions.contains("x - y ≤ -6"));

        let state_1 = automaton
            .guard(state.clone(), &Traversal::step(e13.into(), loc3.into()))
            .unwrap();

        // -x < -15 ∧ x - y ≤ -6 ∧ -y < -21 ∧ y - x < 23
        let conjunctions = state_1.ref_zone().fmt_conjunctions(&labels);
        assert!(conjunctions.contains("-x < -10"));
        assert!(conjunctions.contains("x - y ≤ -6"));
        assert!(conjunctions.contains("-y < -16"));
        assert!(conjunctions.contains("y - x < 23"));

        let state_interval = state.ref_zone().interval();
        let state_interval_0 = state_0.ref_zone().interval();
        let state_interval_1 = state_1.ref_zone().interval();

        assert_eq!("[0, ∞]", state_interval.to_string());
        assert_eq!("[0, 15]", state_interval_0.to_string());
        assert_eq!("(10, ∞]", state_interval_1.to_string());
        
        let delyed_by_0 = state.ref_zone().delayed_by(state_0.ref_zone());
        assert_eq!("[0, 15]", delyed_by_0.to_string());

        let delyed_by_1 = state.ref_zone().delayed_by(state_1.ref_zone());
        assert_eq!("(10, ∞]", delyed_by_1.to_string());

        let intersection = delyed_by_0.intersection(&delyed_by_1);
        assert!(intersection.is_some());

        let intersection = intersection.unwrap();
        assert_eq!("(10, 15]", intersection.to_string());

        let lower_difference_0 = intersection.lower() - delyed_by_0.lower();
        let upper_difference_0 = lower_difference_0 + intersection.included();
        assert_eq!("(10, <)", lower_difference_0.to_string()); // Required expansion to fit intersection.
        assert_eq!("(15, <)", upper_difference_0.to_string());

        let lower_difference_1 = intersection.lower() - delyed_by_1.lower();
        let upper_difference_1 = lower_difference_1 + intersection.included();
        assert_eq!("(0, ≤)", lower_difference_1.to_string());
        assert_eq!("(5, ≤)", upper_difference_1.to_string());
    }
}
