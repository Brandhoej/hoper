use crate::zones::{
    constraint::{Relation, Strictness},
};

use super::{
    expressions::{Binary, Comparison, Expression, Unary},
    literal::Literal,
    statements::Statement,
    tiots::Valuations,
};

pub struct Interpreter {}

impl Interpreter {
    pub const fn new() -> Self {
        Self {}
    }

    pub fn expression(&self, valuations: Valuations, expression: &Expression) -> Valuations {
        match expression {
            Expression::Unary(unary, operand) => match unary {
                Unary::Inverse => self.expression(valuations, &operand).inverse(),
            },
            Expression::Binary(lhs, operator, rhs) => match operator {
                Binary::Conjunction => self
                    .expression(valuations.clone(), &lhs)
                    .union(self.expression(valuations, &rhs)),
                Binary::Disjunction => self
                    .expression(valuations.clone(), &lhs)
                    .intersection(self.expression(valuations, &rhs)),
            },
            Expression::Group(expression) => self.expression(valuations, expression),
            Expression::ClockConstraint(clock, comparison, limit) => match comparison {
                Comparison::LessThanOrEqual => valuations
                    .set_clock_upper_limit(*clock, Relation::new(*limit, Strictness::Weak)),
                Comparison::LessThan => valuations
                    .set_clock_upper_limit(*clock, Relation::new(*limit, Strictness::Strict)),
                Comparison::Equal => valuations.set_clock_limit(*clock, *limit),
                Comparison::GreaterThanOrEqual => valuations
                    .set_clock_lower_limit(*clock, Relation::new(*limit, Strictness::Weak)),
                Comparison::GreaterThen => valuations
                    .set_clock_lower_limit(*clock, Relation::new(*limit, Strictness::Strict)),
            },
            Expression::DiagonalClockConstraint(lhs, rhs, comparison, limit) => match comparison {
                Comparison::LessThanOrEqual => valuations.set_diagonal_constraint(
                    *lhs,
                    *rhs,
                    Relation::new(*limit, Strictness::Weak),
                ),
                Comparison::LessThan => valuations.set_diagonal_constraint(
                    *lhs,
                    *rhs,
                    Relation::new(*limit, Strictness::Strict),
                ),
                Comparison::Equal => valuations.set_clocks_to_be_equal(*lhs, *rhs, *limit),
                Comparison::GreaterThanOrEqual => valuations.set_diagonal_constraint(
                    *rhs,
                    *lhs,
                    Relation::new(*limit, Strictness::Weak),
                ),
                Comparison::GreaterThen => valuations.set_diagonal_constraint(
                    *rhs,
                    *lhs,
                    Relation::new(*limit, Strictness::Strict),
                ),
            },
            Expression::Literal(literal) => todo!(),
        }
    }

    pub fn statement(&self, valuations: Valuations, statement: &Statement) -> Valuations {
        match statement {
            Statement::Sequence(statements) | Statement::Branch(statements) => {
                statements.iter().fold(valuations, |valuations, statement| {
                    self.statement(valuations, statement)
                })
            }
            Statement::Expression(expression) => self.expression(valuations, expression),
        }
    }
}
