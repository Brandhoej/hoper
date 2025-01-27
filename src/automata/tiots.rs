use crate::{
    automata::extrapolator::Extrapolator,
    zones::{
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
    tioa::{LocationTree, Move, TIOA},
};

#[derive(Clone)]
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

    pub const fn zone(&self) -> &DBM<Canonical> {
        &self.zone
    }

    pub fn decompose(self) -> (LocationTree, DBM<Canonical>, Environment) {
        (self.location, self.zone, self.environment)
    }
}

#[derive(Clone)]
pub enum Transition {
    Synchronisation { action: Action, destination: State },
    Silent { destination: State },
}

impl Transition {
    pub const fn new_synchronisation(action: Action, destination: State) -> Self {
        Self::Synchronisation {
            action,
            destination,
        }
    }

    pub const fn new_silent(destination: State) -> Self {
        Self::Silent { destination }
    }

    pub fn action(&self) -> Option<Action> {
        match self {
            Transition::Synchronisation { action, .. } => Some(*action),
            Transition::Silent { .. } => None,
        }
    }

    pub fn destination(&self) -> &State {
        match self {
            Transition::Synchronisation { destination, .. } => destination,
            Transition::Silent { destination } => destination,
        }
    }
}

pub trait TIOTS
where
    Self: TA + IOA,
{
    fn initial_state(&self) -> State;
    fn transitions(
        &self,
        source: State,
        moves: impl Iterator<Item = Move>,
    ) -> impl Iterator<Item = Transition>;
    fn traverse_from(
        &self,
        source: State,
        action: Action,
    ) -> Result<impl Iterator<Item = Transition>, ()>;
    fn states_from(
        &self,
        source: State,
        action: Action,
    ) -> Result<impl Iterator<Item = State>, ()> {
        match self.traverse_from(source, action) {
            Ok(transitions) => {
                Ok(transitions.map(|transition| transition.destination().to_owned()))
            }
            Err(_) => Err(()),
        }
    }
}

impl<T: ?Sized + TIOA> TIOTS for T {
    fn initial_state(&self) -> State {
        let location = self.initial_location();
        let invariant = self.location(&self.initial_location()).unwrap().invariant();
        let zone = DBM::universe(self.clocks().len() as Clock);
        match Extrapolator::new().expression(zone.dirty(), &invariant) {
            Ok(zone) => State::new(location, zone, self.into()),
            Err(_) => panic!("a TIOTS should have an initial state"),
        }
    }

    fn transitions(
        &self,
        source: State,
        moves: impl Iterator<Item = Move>,
    ) -> impl Iterator<Item = Transition> {
        let is_empty = source.zone.is_empty();
        let mut extrapolator = Extrapolator::new();
        let mut interpreter = Interpreter::new();

        moves
            .filter_map(move |m| {
                if is_empty {
                    return None;
                }

                let mut zone = source.zone.clone();

                // If there is a edge we have to first check the guard and then traverse it.
                if let Some(edge) = m.edge() {
                    // diagonal constraints, upper/lower bounds, and such.
                    match extrapolator.expression(zone.dirty(), edge.guard()) {
                        Ok(extrapolation) => zone = extrapolation,
                        Err(_) => return None,
                    }

                    // Resets, copies, and such.
                    zone = interpreter.statement(zone, edge.update());
                }

                // We have traversed the edge (if any) now we relax which is assumed indefinite.
                // However, this will later be restricted by the location's invariant.
                zone.up();

                // At the end of the move we have to check the invariant it it is satified.
                let location = self.location(m.location()).unwrap();
                match extrapolator.expression(zone.dirty(), &location.invariant()) {
                    Ok(extrapolation) => zone = extrapolation,
                    Err(_) => return None,
                }

                let destination =
                    State::new(m.location().clone(), zone, source.environment.clone());

                Some(match m {
                    Move::To { edge, .. } => {
                        Transition::new_synchronisation(*edge.action(), destination)
                    }
                    Move::Stay { .. } => Transition::new_silent(destination),
                })
            })
            .into_iter()
    }

    fn traverse_from(
        &self,
        source: State,
        action: Action,
    ) -> Result<impl Iterator<Item = Transition>, ()> {
        match TIOA::outgoing(self, source.location(), action) {
            Ok(transitions) => Ok(self.transitions(source.clone(), transitions.into_iter())),
            Err(_) => Err(()),
        }
    }
}
