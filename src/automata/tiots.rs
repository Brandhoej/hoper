use crate::zones::federation::Federation;

use super::{
    action::Action,
    extrapolator::Extrapolator,
    ioa::IOA,
    ta::TA,
    tioa::{LocationTree, TIOA},
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

    pub const fn valuations(&self) -> &Federation {
        &self.federation
    }
}

#[derive(Clone)]
pub struct Transition {
    action: Action,
    destination: State,
}

impl Transition {
    pub const fn new(action: Action, destination: State) -> Self {
        Self {
            action,
            destination,
        }
    }

    pub fn action(&self) -> &Action {
        &self.action
    }

    pub fn destination(&self) -> &State {
        &self.destination
    }
}

pub trait TIOTS
where
    Self: TA + IOA,
{
    fn initial(&self) -> State;
    fn transitions(&self, source: State, action: Action) -> Result<Vec<Transition>, ()>;
}

impl<T: TIOA> TIOTS for T {
    fn initial(&self) -> State {
        let clocks = self.clocks();
        let federation = Federation::zero(clocks);
        let location = TIOA::initial(self);
        State::new(location, federation)
    }

    fn transitions(&self, source: State, action: Action) -> Result<Vec<Transition>, ()> {
        let mut extrapolator = Extrapolator::empty();

        match self.outgoing(source.location(), action) {
            Ok(outgoings) => {
                let transitions = outgoings
                    .iter()
                    .filter_map(|m| {
                        None
                        /*let mut destination = source.clone();

                        // If there is a edge we have to first check the guard and then traverse it.
                        if let Some(edge) = m.edge() {
                            interpreter.expression(&mut destination, edge.guard());
                            if !interpreter.pop().unwrap().boolean().unwrap() {
                                return None;
                            }

                            interpreter.statement(&mut destination, edge.update());
                        }

                        let location = self.location(m.location()).unwrap();

                        // At the end of the move we have to check the invariant it it is satified.
                        interpreter.expression(&mut destination, &location.invariant());
                        if !interpreter.pop().unwrap().boolean().unwrap() {
                            return None;
                        }

                        Some(Transition::new(action, destination))*/
                    })
                    .collect();
                Ok(transitions)
            }
            Err(err) => Err(err),
        }
    }
}
