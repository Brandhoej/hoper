use std::fmt::{self, Display};

use super::{
    literal::{ContextualLiteral, Literal},
    partitioned_symbol_table::{PartitionedSymbol, PartitionedSymbolTable},
};

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

    pub fn conjoin_all(self, rhs: Vec<Self>) -> Self {
        if rhs.is_empty() {
            return self;
        }

        let mut expressions = vec![self];
        expressions.extend(rhs);
        Self::conjunctions(expressions)
    }

    pub fn disjoin_all(self, rhs: Vec<Self>) -> Self {
        if rhs.is_empty() {
            return self;
        }

        let mut expressions = vec![self];
        expressions.extend(rhs);
        Self::disjunctions(expressions)
    }

    pub fn conjunctions(expressions: Vec<Self>) -> Self {
        Self::left_fold_binary(expressions, Binary::Conjunction)
    }

    pub fn disjunctions(expressions: Vec<Self>) -> Self {
        Self::left_fold_binary(expressions, Binary::Disjunction)
    }

    pub fn conjunction(self, rhs: Self) -> Self {
        Self::Binary(Box::new(self), Binary::Conjunction, Box::new(rhs))
    }

    pub fn disjunction(self, rhs: Self) -> Self {
        Self::Binary(Box::new(self), Binary::Disjunction, Box::new(rhs))
    }

    pub fn in_context<'a>(
        &'a self,
        symbols: &'a PartitionedSymbolTable,
    ) -> ContextualExpression<'a> {
        ContextualExpression::new(symbols, self)
    }
}

impl From<Literal> for Expression {
    fn from(literal: Literal) -> Self {
        Self::Literal(literal)
    }
}

impl From<PartitionedSymbol> for Expression {
    fn from(value: PartitionedSymbol) -> Self {
        Expression::Literal(value.into())
    }
}

impl From<i16> for Expression {
    fn from(value: i16) -> Self {
        Self::Literal(value.into())
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Unary(operator, operand) => write!(f, "{}{}", operator, operand),
            Expression::Binary(lhs, operator, rhs) => write!(f, "{} {} {}", lhs, operator, rhs),
            Expression::Group(expression) => write!(f, "({})", expression),
            Expression::Literal(literal) => write!(f, "{}", literal),
            Expression::ClockConstraint(operand, comparison, bound) => {
                write!(f, "{} {} {}", operand, comparison, bound)
            }
            Expression::DiagonalClockConstraint(lhs, rhs, comparison, bound) => {
                write!(f, "{} - {} {} {}", lhs, rhs, comparison, bound)
            }
        }
    }
}

pub struct ContextualExpression<'a> {
    symbols: &'a PartitionedSymbolTable,
    expression: &'a Expression,
}

impl<'a> ContextualExpression<'a> {
    pub const fn new(symbols: &'a PartitionedSymbolTable, expression: &'a Expression) -> Self {
        Self {
            symbols,
            expression,
        }
    }
}

impl<'a> Display for ContextualExpression<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let in_context = |expr: &'a Expression| -> ContextualExpression<'a> {
            ContextualExpression::new(self.symbols, expr)
        };

        match self.expression {
            Expression::Unary(operator, operand) => {
                write!(f, "{}{}", operator, in_context(operand))
            }
            Expression::Binary(lhs, operator, rhs) => {
                write!(f, "{} {} {}", in_context(lhs), operator, in_context(rhs))
            }
            Expression::Group(expression) => write!(f, "({})", in_context(expression)),
            Expression::Literal(literal) => {
                write!(f, "{}", ContextualLiteral::new(self.symbols, literal))
            }
            Expression::ClockConstraint(operand, comparison, bound) => {
                write!(
                    f,
                    "{} {} {}",
                    in_context(operand),
                    comparison,
                    in_context(bound)
                )
            }
            Expression::DiagonalClockConstraint(lhs, rhs, comparison, bound) => {
                write!(
                    f,
                    "{} - {} {} {}",
                    in_context(lhs),
                    in_context(rhs),
                    comparison,
                    in_context(bound)
                )
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::automata::{literal::Literal, partitioned_symbol_table::PartitionedSymbolTable};

    use super::Expression;

    #[test]
    fn contextual_expression_display() {
        let symbols = PartitionedSymbolTable::new();
        let a: Expression = Literal::new_identifier(symbols.intern(0, "a")).into();
        let b: Expression = Literal::new_identifier(symbols.intern(0, "b")).into();

        assert_eq!(a.conjunction(b).in_context(&symbols).to_string(), "a ∧ b");
    }
}
