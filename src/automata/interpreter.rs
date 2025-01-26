use crate::zones::dbm::{Canonical, DBM};

use super::{expressions::Expression, literal::Literal, statements::Statement};

pub struct Interpreter {
    stack: Vec<Literal>,
}

impl Interpreter {
    pub fn empty() -> Self {
        Self { stack: Vec::new() }
    }

    pub fn expression(&mut self, zone: &DBM<Canonical>, expression: &Expression) {}

    pub fn statement(&mut self, mut zone: DBM<Canonical>, statement: &Statement) -> DBM<Canonical> {
        match statement {
            Statement::Sequence(statements) => {
                for statement in statements.into_iter() {
                    zone = self.statement(zone, statement)
                }
                zone
            }
            Statement::Branch(branches) => {
                for branch in branches.into_iter() {
                    zone = self.statement(zone, branch)
                }
                zone
            }
            Statement::Expression(expression) => {
                self.expression(&zone, expression);
                zone
            }
            Statement::FreeClock(clock) => {
                zone.free(*clock);
                zone
            }
        }
    }
}
