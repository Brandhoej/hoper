use crate::zones::dbm::{Canonical, DBM};

use super::{expressions::Expression, literal::Literal, statements::Statement, tiots::State};

pub struct Interpreter {
    stack: Vec<Literal>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self { stack: Vec::new() }
    }

    pub fn expression(&mut self, state: &State, expression: &Expression) {}

    pub fn statement(&mut self, mut state: State, statement: &Statement) -> State {
        match statement {
            Statement::Sequence(statements) => {
                for statement in statements.into_iter() {
                    state = self.statement(state, statement)
                }
                state
            }
            Statement::Branch(branches) => {
                for branch in branches.into_iter() {
                    state = self.statement(state, branch)
                }
                state
            }
            Statement::Expression(expression) => {
                todo!()
            }
            Statement::Reset(clock, limit) => {
                let clock = state.ref_environemnt().get_clock(*clock).unwrap();
                state.mut_zone().reset(clock, *limit);
                state
            }
        }
    }
}
