use std::fmt::{self, Display};

use crate::zones::constraint::{Clock, Constraint, Limit, Relation};

use super::literal::Literal;

#[derive(Clone, Debug)]
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

#[derive(Clone, Debug)]
pub enum Unary {
    LogicalNegation,
}

impl Display for Unary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Unary::LogicalNegation => write!(f, "¬"),
        }
    }
}

#[derive(Clone, Debug)]
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

#[derive(Clone, Debug)]
pub enum Expression {
    Unary(Unary, Box<Expression>),
    Binary(Box<Expression>, Binary, Box<Expression>),
    Group(Box<Expression>),
    Literal(Literal),
    ClockConstraint(Box<Expression>, Comparison, Box<Expression>),
    DiagonalClockConstraint(
        Box<Expression>,
        Box<Expression>,
        Comparison,
        Box<Expression>,
    ),
}

impl Expression {
    pub fn new_clock_constraint(operand: Self, comparison: Comparison, limit: Self) -> Self {
        Self::ClockConstraint(Box::new(operand), comparison, Box::new(limit))
    }

    pub fn not(self) -> Self {
        Self::Unary(Unary::LogicalNegation, Box::new(self))
    }

    pub fn left_fold_binary(expressions: Vec<Self>, binary: Binary) -> Self {
        if expressions.is_empty() {
            panic!()
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

    pub fn conjoin(self, rhs: Vec<Self>) -> Self {
        if rhs.is_empty() {
            return self;
        }

        let mut expressions = vec![self];
        expressions.extend(rhs);
        Self::conjunction(expressions)
    }

    pub fn disjoin(self, rhs: Vec<Self>) -> Self {
        if rhs.is_empty() {
            return self;
        }

        let mut expressions = vec![self];
        expressions.extend(rhs);
        Self::disjunction(expressions)
    }

    pub fn conjunction(expressions: Vec<Self>) -> Self {
        Self::left_fold_binary(expressions, Binary::Conjunction)
    }

    pub fn disjunction(expressions: Vec<Self>) -> Self {
        Self::left_fold_binary(expressions, Binary::Disjunction)
    }
}

impl From<Literal> for Expression {
    fn from(literal: Literal) -> Self {
        Self::Literal(literal)
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Unary(operator, operand) => write!(f, "{}{}", operator, operand),
            Expression::Binary(lhs, operator, rhs) => write!(f, "{}{}{}", lhs, operator, rhs),
            Expression::Group(expression) => write!(f, "({})", expression),
            Expression::Literal(literal) => write!(f, "{}", literal),
            Expression::ClockConstraint(operand, comparison, bound) => {
                write!(f, "{} {} {}", *operand, comparison, bound)
            }
            Expression::DiagonalClockConstraint(lhs, rhs, comparison, bound) => {
                write!(f, "{} - {} {} {}", *lhs, *rhs, comparison, bound)
            }
        }
    }
}
