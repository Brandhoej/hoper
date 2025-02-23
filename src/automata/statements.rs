use std::fmt::{self, Display, Formatter};

use itertools::Itertools;

use crate::zones::constraint::Limit;

use super::{
    expressions::Expression,
    partitioned_symbol_table::{PartitionedSymbol, PartitionedSymbolTable},
};

#[derive(Clone, Debug)]
pub enum Statement {
    Sequence(Vec<Statement>),
    Branch(Vec<Statement>),
    Expression(Expression),
    Reset(PartitionedSymbol, Limit),
}

impl Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Expression(expression) => writeln!(f, "{}", expression),
            Statement::Sequence(statements) | Statement::Branch(statements) => {
                if statements.is_empty() {
                    return write!(f, "");
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

    pub const fn reset(clock: PartitionedSymbol, limit: Limit) -> Self {
        Self::Reset(clock, limit)
    }

    pub fn in_context<'a>(
        &'a self,
        symbols: &'a PartitionedSymbolTable,
    ) -> ContextualStatement<'a> {
        ContextualStatement::new(symbols, self)
    }
}

impl From<Expression> for Statement {
    fn from(expression: Expression) -> Self {
        Self::Expression(expression)
    }
}

pub struct ContextualStatement<'a> {
    symbols: &'a PartitionedSymbolTable,
    statement: &'a Statement,
}

impl<'a> ContextualStatement<'a> {
    pub const fn new(symbols: &'a PartitionedSymbolTable, statement: &'a Statement) -> Self {
        Self { symbols, statement }
    }
}

impl<'a> Display for ContextualStatement<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.statement {
            Statement::Expression(expression) => {
                writeln!(f, "{}", expression.in_context(self.symbols))
            }
            Statement::Sequence(statements) | Statement::Branch(statements) => {
                if statements.is_empty() {
                    return write!(f, "");
                }

                let separator = if matches!(self.statement, Statement::Sequence(_)) {
                    "; "
                } else {
                    " || "
                };
                let join = statements
                    .iter()
                    .filter_map(|statement| {
                        let string = statement.in_context(&self.symbols).to_string();
                        if string.len() == 0 {
                            None
                        } else {
                            Some(string)
                        }
                    })
                    .join(separator);
                write!(f, "{}", join)
            }
            Statement::Reset(symbol, limit) => {
                write!(f, "{} = {}", self.symbols.resolve(symbol), limit)
            }
        }
    }
}
