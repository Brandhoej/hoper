use std::fmt::{self, Display};

use crate::zones::constraint::{Clock, Limit};

use super::literal::Literal;

#[derive(Clone)]
pub enum Binary {
    Conjunction,
    Disjunction,
}

impl Display for Binary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Binary::Conjunction => write!(f, "∧"),
            Binary::Disjunction => write!(f, "∨"),
        }
    }
}

#[derive(Clone)]
pub enum Unary {
    Inverse,
}

impl Display for Unary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Unary::Inverse => write!(f, "¬"),
        }
    }
}

#[derive(Clone)]
pub enum Comparison {
    LessThanOrEqual,
    LessThan,
    Equal,
    GreaterThanOrEqual,
    GreaterThan,
}

impl Display for Comparison {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Comparison::LessThanOrEqual => write!(f, "≤"),
            Comparison::LessThan => write!(f, "<"),
            Comparison::Equal => write!(f, "=="),
            Comparison::GreaterThanOrEqual => write!(f, "≥"),
            Comparison::GreaterThan => write!(f, ">"),
        }
    }
}

#[derive(Clone)]
pub enum Expression {
    Unary(Unary, Box<Expression>),
    Binary(Box<Expression>, Binary, Box<Expression>),
    Group(Box<Expression>),
    Literal(Literal),
    ClockConstraint(Clock, Comparison, Limit),
    DiagonalClockConstraint(Clock, Clock, Comparison, Limit),
}

impl Expression {
    pub const fn boolean(value: bool) -> Self {
        Self::Literal(Literal::new_boolean(value))
    }

    pub const fn new_true() -> Self {
        Self::Literal(Literal::new_true())
    }

    pub const fn new_false() -> Self {
        Self::Literal(Literal::new_false())
    }

    pub fn not(self) -> Self {
        Expression::Unary(Unary::Inverse, Box::new(self))
    }

    pub fn left_fold_binary(expressions: Vec<Expression>, binary: Binary) -> Expression {
        if expressions.is_empty() {
            return Self::new_true();
        }

        if expressions.len() == 1 {
            return expressions[0].to_owned();
        }

        let mut iter = expressions.into_iter();
        let mut result = iter.next().unwrap();

        for expr in iter {
            result = Self::Binary(Box::new(result), binary.clone(), Box::new(expr));
        }

        result
    }

    pub fn conjoin(self, rhs: Vec<Expression>) -> Expression {
        if rhs.is_empty() {
            return self;
        }

        let mut expressions = vec![self];
        expressions.extend(rhs);
        Self::conjunction(expressions)
    }

    pub fn disjoin(self, rhs: Vec<Expression>) -> Expression {
        if rhs.is_empty() {
            return self;
        }

        let mut expressions = vec![self];
        expressions.extend(rhs);
        Self::disjunction(expressions)
    }

    pub fn conjunction(expressions: Vec<Expression>) -> Expression {
        Expression::left_fold_binary(expressions, Binary::Conjunction)
    }

    pub fn disjunction(expressions: Vec<Expression>) -> Expression {
        Expression::left_fold_binary(expressions, Binary::Disjunction)
    }
}

impl From<Literal> for Expression {
    fn from(value: Literal) -> Self {
        Expression::Literal(value)
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Unary(operator, operand) => write!(f, "{}{}", operator, operand),
            Expression::Binary(lhs, operator, rhs) => write!(f, "{}{}{}", lhs, operator, rhs),
            Expression::Group(expression) => write!(f, "({})", expression),
            Expression::Literal(value) => match value {
                Literal::Boolean(value) => write!(f, "{}", *value),
            },
            Expression::ClockConstraint(operand, comparison, bound) => {
                write!(f, "{} {} {}", *operand, comparison, bound)
            }
            Expression::DiagonalClockConstraint(lhs, rhs, comparison, bound) => {
                write!(f, "{} - {} {} {}", *lhs, *rhs, comparison, bound)
            }
        }
    }
}
