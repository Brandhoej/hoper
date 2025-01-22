use crate::zones::{
    constraint::{Limit, Relation, Strictness, REFERENCE},
    federation::Federation,
};

use super::{
    expressions::{Binary, Comparison, Expression},
    literal::Literal,
    statements::Statement,
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

    pub fn expression(
        &mut self,
        mut federation: Federation,
        expression: &Expression,
    ) -> Federation {
        match expression {
            Expression::Unary(unary, expression) => {
                federation = self.expression(federation, expression);
                let value = self.stack.pop().unwrap();

                match unary {
                    super::expressions::Unary::LogicalNegation => {
                        let negation = Literal::Boolean(!value.boolean().unwrap());
                        self.stack.push(negation);
                        return federation.inverse();
                    }
                }
            }
            Expression::Binary(lhs, binary, rhs) => {
                federation = self.expression(federation, &lhs);
                match binary {
                    Binary::Conjunction => {
                        let lhs_federation = self.expression(federation.clone(), &lhs);
                        let lhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                        if !lhs_bool {
                            self.stack.push(Literal::new_false());
                            return federation.clear();
                        }

                        let rhs_federation = self.expression(federation.clone(), &rhs);
                        let rhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                        if !rhs_bool {
                            self.stack.push(Literal::new_false());
                            return federation.clear();
                        }

                        self.stack.push(Literal::new_true());
                        lhs_federation.intersection(rhs_federation)
                    }
                    Binary::Disjunction => {
                        let mut lhs_federation = self.expression(federation.clone(), &lhs);
                        let lhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                        let rhs_federation = self.expression(federation.clone(), &rhs);
                        let rhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                        self.stack.push(Literal::new_boolean(lhs_bool || rhs_bool));

                        if lhs_bool && rhs_bool {
                            lhs_federation.union(rhs_federation);
                            return lhs_federation;
                        } else if lhs_bool {
                            return lhs_federation;
                        } else if rhs_bool {
                            return rhs_federation;
                        } else {
                            federation.clear()
                        }
                    }
                }
            }
            Expression::Group(expression) => self.expression(federation, expression),
            Expression::Literal(value) => {
                self.stack.push(value.clone());
                federation
            }
            Expression::ClockConstraint(operand, comparison, limit) => {
                federation = self.expression(federation, &operand);
                let clock = self.stack.pop().unwrap().clock().unwrap();

                federation = self.expression(federation, &limit);
                let limit_literal = self.stack.pop().unwrap().i16().unwrap();

                match comparison {
                    Comparison::LessThanOrEqual => federation
                        .tighten_upper(clock, Relation::new(limit_literal, Strictness::Weak)),
                    Comparison::LessThan => federation
                        .tighten_upper(clock, Relation::new(limit_literal, Strictness::Strict)),
                    Comparison::Equal => federation.tighten_limit(clock, REFERENCE, limit_literal),
                    Comparison::GreaterThanOrEqual => federation
                        .tighten_lower(clock, Relation::new(limit_literal, Strictness::Weak)),
                    Comparison::GreaterThan => federation
                        .tighten_lower(clock, Relation::new(limit_literal, Strictness::Strict)),
                }
            }
            Expression::DiagonalClockConstraint(minuend, subtrahend, comparison, limit) => {
                federation = self.expression(federation, &minuend);
                let minuend_clock = self.stack.pop().unwrap().clock().unwrap();

                federation = self.expression(federation, &subtrahend);
                let subtrahend_clock = self.stack.pop().unwrap().clock().unwrap();

                federation = self.expression(federation, &limit);
                let limit_literal = self.stack.pop().unwrap().i16().unwrap();

                match comparison {
                    Comparison::LessThanOrEqual => federation.tighten_relation(
                        minuend_clock,
                        subtrahend_clock,
                        Relation::new(limit_literal, Strictness::Weak),
                    ),
                    Comparison::LessThan => federation.tighten_relation(
                        minuend_clock,
                        subtrahend_clock,
                        Relation::new(limit_literal, Strictness::Strict),
                    ),
                    Comparison::Equal => {
                        federation.tighten_limit(minuend_clock, subtrahend_clock, limit_literal)
                    }
                    Comparison::GreaterThanOrEqual => federation.tighten_relation(
                        subtrahend_clock,
                        minuend_clock,
                        Relation::new(limit_literal, Strictness::Weak),
                    ),
                    Comparison::GreaterThan => federation.tighten_relation(
                        subtrahend_clock,
                        minuend_clock,
                        Relation::new(limit_literal, Strictness::Strict),
                    ),
                }
            }
        }
    }

    pub fn statement(&mut self, federation: Federation, statement: &Statement) -> Federation {
        match statement {
            Statement::Sequence(statements) | Statement::Branch(statements) => {
                statements.iter().fold(federation, |federation, statement| {
                    self.statement(federation, statement)
                })
            }
            Statement::Expression(expression) => self.expression(federation, expression),
            Statement::FreeClock(clock) => federation.free(*clock),
        }
    }

    pub fn extrapolate_expression(federation: Federation, expression: &Expression) -> Federation {
        Extrapolator::empty().expression(federation, expression)
    }

    pub fn extrapolate_statement(federation: Federation, statement: &Statement) -> Federation {
        Extrapolator::empty().statement(federation, statement)
    }
}
