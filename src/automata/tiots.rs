use crate::zones::federation::Federation;

use super::{
    action::Action,
    extrapolator::Extrapolator,
    ioa::IOA,
    ta::TA,
    tioa::{LocationTree, Move, TIOA},
};

#[derive(Clone)]
pub struct State {
    location: LocationTree,
    federation: Federation,
}

impl State {
    pub const fn new(location: LocationTree, federation: Federation) -> Self {
        Self {
            location,
            federation,
        }
    }

    pub const fn location(&self) -> &LocationTree {
        &self.location
    }

    pub const fn federation(&self) -> &Federation {
        &self.federation
    }

    pub fn decompose(self) -> (LocationTree, Federation) {
        (self.location, self.federation)
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
        let location = TIOA::initial_location(self);
        let federation = Extrapolator::extrapolate_expression(
            Federation::universe(self.clocks()),
            &self.location(&location).unwrap().invariant(),
        );
        State::new(location, federation)
    }

    fn transitions(
        &self,
        source: State,
        moves: impl Iterator<Item = Move>,
    ) -> impl Iterator<Item = Transition> {
        let is_empty = source.federation.is_empty();
        let mut extrapolator = Extrapolator::empty();

        moves
            .filter_map(move |m| {
                if is_empty {
                    return None;
                }

                let mut federation = source.federation.clone();

                // If there is a edge we have to first check the guard and then traverse it.
                if let Some(edge) = m.edge() {
                    // diagonal constraints, upper/lower bounds, and such.
                    federation = extrapolator.expression(federation, edge.guard());
                    if federation.is_empty() {
                        return None;
                    }

                    // Resets, copies, and such.
                    federation = extrapolator.statement(federation, edge.update());
                }

                // We have traversed the edge (if any) now we relax which is assumed indefinite.
                // However, this will later be restricted by the location's invariant.
                federation = federation.up();

                // At the end of the move we have to check the invariant it it is satified.
                let location = self.location(m.location()).unwrap();
                federation = extrapolator.expression(federation, &location.invariant());
                if federation.is_empty() {
                    return None;
                }

                let destination = State::new(m.location().clone(), federation);

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
