use crate::zones::{
    constraint::{Relation, Strictness, REFERENCE},
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
                            return federation.clear();
                        }

                        let rhs_federation = self.expression(federation.clone(), &rhs);
                        let rhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                        if !rhs_bool {
                            return federation.clear();
                        }

                        lhs_federation.intersection(rhs_federation)
                    }
                    Binary::Disjunction => {
                        let mut lhs_federation = self.expression(federation.clone(), &lhs);
                        let lhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                        let rhs_federation = self.expression(federation.clone(), &rhs);
                        let rhs_bool = self.stack.pop().unwrap().boolean().unwrap();

                        if lhs_bool && rhs_bool {
                            lhs_federation.union(rhs_federation);
                            return lhs_federation;
                        } else if lhs_bool {
                            return lhs_federation;
                        } else if rhs_bool {
                            return rhs_federation;
                        }
                        federation.clear()
                    }
                }
            }
            Expression::Group(expression) => self.expression(federation, expression),
            Expression::Literal(value) => {
                self.stack.push(value.clone());
                federation
            }
            Expression::ClockConstraint(clock, comparison, limit) => match comparison {
                Comparison::LessThanOrEqual => {
                    federation.tighten_upper(*clock, Relation::new(*limit, Strictness::Weak))
                }
                Comparison::LessThan => {
                    federation.tighten_upper(*clock, Relation::new(*limit, Strictness::Strict))
                }
                Comparison::Equal => federation.tighten_limit(*clock, REFERENCE, *limit),
                Comparison::GreaterThanOrEqual => {
                    federation.tighten_lower(*clock, Relation::new(*limit, Strictness::Weak))
                }
                Comparison::GreaterThan => {
                    federation.tighten_lower(*clock, Relation::new(*limit, Strictness::Strict))
                }
            },
            Expression::DiagonalClockConstraint(lhs, rhs, comparison, limit) => match comparison {
                Comparison::LessThanOrEqual => {
                    federation.tighten_relation(*lhs, *rhs, Relation::new(*limit, Strictness::Weak))
                }
                Comparison::LessThan => federation.tighten_relation(
                    *lhs,
                    *rhs,
                    Relation::new(*limit, Strictness::Strict),
                ),
                Comparison::Equal => federation.tighten_limit(*lhs, *rhs, *limit),
                Comparison::GreaterThanOrEqual => {
                    federation.tighten_relation(*rhs, *lhs, Relation::new(*limit, Strictness::Weak))
                }
                Comparison::GreaterThan => federation.tighten_relation(
                    *rhs,
                    *lhs,
                    Relation::new(*limit, Strictness::Strict),
                ),
            },
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
        }
    }
}
