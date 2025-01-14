use crate::zones::constraint::{Relation, Strictness};

use super::{
    expressions::{Binary, Comparison, Expression, Unary},
    literal::Literal,
    statements::Statement,
    tiots::Valuations,
};

pub struct Extrapolator {
    stack: Vec<Literal>,
}

impl Extrapolator {
    pub const fn new(stack: Vec<Literal>) -> Self {
        Self { stack }
    }

    pub const fn empty() -> Self {
        Self::new(vec![])
    }

    pub fn expression(&mut self, mut valuations: Valuations, expression: &Expression) -> Valuations {
        match expression {
            Expression::Unary(unary, operand) => match unary {
                Unary::Inverse => self.expression(valuations, &operand).inverse(),
            },
            Expression::Binary(lhs, operator, rhs) => match operator {
                Binary::Conjunction => {
                    valuations = self.expression(valuations.clone(), &lhs);
                    if self.stack.pop().unwrap().boolean().unwrap() {
                        valuations = self.expression(valuations, &rhs);
                        if self.stack.pop().unwrap().boolean().unwrap() {
                            valuations
                        } else {
                            valuations.clear()
                        }
                    } else {
                        valuations.clear()
                    }
                }
                Binary::Disjunction => {
                    valuations = self.expression(valuations.clone(), &lhs);
                    if !self.stack.pop().unwrap().boolean().unwrap() {
                        valuations = self.expression(valuations, &rhs);
                    }

                    if self.stack.last().unwrap().boolean().unwrap() {
                        valuations
                    } else {
                        valuations.clear()
                    }
                },
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
                Comparison::GreaterThan => valuations
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
                Comparison::GreaterThan => valuations.set_diagonal_constraint(
                    *rhs,
                    *lhs,
                    Relation::new(*limit, Strictness::Strict),
                ),
            },
            Expression::Literal(literal) => {
                self.stack.push(literal.clone());
                valuations
            }
        }
    }

    pub fn statement(&mut self, valuations: Valuations, statement: &Statement) -> Valuations {
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
