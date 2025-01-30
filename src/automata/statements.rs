use std::fmt::{self, Display};

use itertools::Itertools;
use symbol_table::Symbol;

use crate::zones::constraint::Limit;

use super::expressions::Expression;

#[derive(Clone, Debug)]
pub enum Statement {
    Sequence(Vec<Statement>),
    Branch(Vec<Statement>),
    Expression(Expression),
    Reset(Symbol, Limit),
}

impl Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Expression(expression) => writeln!(f, "{}", expression),
            Statement::Sequence(statements) | Statement::Branch(statements) => {
                if statements.is_empty() {
                    return write!(f, ";");
                }

                let separator = if matches!(self, Statement::Sequence(_)) {
                    "; "
                } else {
                    " || "
                };
                let join = statements.iter().map(ToString::to_string).join(separator);
                write!(f, "{}", join)
            }
            Statement::Reset(symbol, limit) => {
                write!(f, "{:?} = {}", symbol, limit)
            }
        }
    }
}

impl Statement {
    pub const fn sequence(statements: Vec<Self>) -> Self {
        Self::Sequence(statements)
    }

    pub const fn empty() -> Self {
        Self::Sequence(vec![])
    }

    pub const fn branch(statements: Vec<Self>) -> Self {
        Self::Branch(statements)
    }

    pub const fn express(expression: Expression) -> Self {
        Self::Expression(expression)
    }
}

impl From<Expression> for Statement {
    fn from(expression: Expression) -> Self {
        Self::Expression(expression)
    }
}
