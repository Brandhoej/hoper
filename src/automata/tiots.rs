use crate::zones::{
    constraint::{Clock, Limit, Relation, REFERENCE},
    federation::Federation,
};

use super::{
    action::Action,
    interpreter::Interpreter,
    ioa::IOA,
    ta::TA,
    tioa::{LocationTree, TIOA},
};

#[derive(Clone)]
pub struct Valuations {
    federation: Federation,
}

impl Valuations {
    pub fn new(clocks: Federation) -> Self {
        Self { federation: clocks }
    }

    pub fn zero(clocks: Clock) -> Self {
        Self::new(Federation::zero(clocks))
    }

    pub fn universe(clocks: Clock) -> Self {
        Self::new(Federation::universe(clocks))
    }

    pub fn clear(mut self) -> Self {
        self.federation = self.federation.clear();
        self
    }

    pub fn inverse(mut self) -> Self {
        self.federation = self.federation.inverse();
        self
    }

    pub fn union(mut self, other: Self) -> Self {
        self.federation.union(other.federation);
        self
    }

    pub fn intersection(mut self, other: Self) -> Self {
        self.federation = self.federation.intersection(other.federation);
        self
    }

    pub fn set_diagonal_constraint(mut self, i: Clock, j: Clock, relation: Relation) -> Self {
        self.federation = self.federation.tighten_relation(i, j, relation);
        self
    }

    pub fn set_clocks_to_be_equal(mut self, i: Clock, j: Clock, limit: Limit) -> Self {
        self.federation = self.federation.tighten_limit(i, j, limit);
        self
    }

    pub fn set_clock_limit(mut self, clock: Clock, limit: Limit) -> Self {
        self.federation = self.federation.tighten_limit(clock, REFERENCE, limit);
        self
    }

    pub fn set_clock_upper_limit(mut self, clock: Clock, relation: Relation) -> Self {
        todo!()
    }

    pub fn set_clock_lower_limit(mut self, clock: Clock, relation: Relation) -> Self {
        todo!()
    }
}

#[derive(Clone)]
pub struct State {
    location: LocationTree,
    valuations: Valuations,
}

impl State {
    pub const fn new(location: LocationTree, valuations: Valuations) -> Self {
        Self {
            location,
            valuations,
        }
    }

    pub const fn location(&self) -> &LocationTree {
        &self.location
    }

    pub const fn valuations(&self) -> &Valuations {
        &self.valuations
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
        let valuations = Valuations::zero(clocks);
        let location = TIOA::initial(self);
        State::new(location, valuations)
    }

    fn transitions(&self, source: State, action: Action) -> Result<Vec<Transition>, ()> {
        let mut interpreter = Interpreter::new();

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
