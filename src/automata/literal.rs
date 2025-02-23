use std::fmt::Display;

use super::partitioned_symbol_table::{PartitionedSymbol, PartitionedSymbolTable};

#[derive(Clone, Debug)]
pub enum Literal {
    Boolean(bool),
    I16(i16),
    Identifier(PartitionedSymbol),
}

impl Literal {
    #[inline]
    pub const fn new_boolean(value: bool) -> Self {
        Self::Boolean(value)
    }

    #[inline]
    pub const fn new_true() -> Self {
        Self::new_boolean(true)
    }

    #[inline]
    pub const fn new_false() -> Self {
        Self::new_boolean(false)
    }

    #[inline]
    pub const fn new_identifier(symbol: PartitionedSymbol) -> Self {
        Self::Identifier(symbol)
    }

    #[inline]
    pub const fn new_i16(value: i16) -> Self {
        Self::I16(value)
    }

    #[inline]
    pub const fn boolean(&self) -> Option<bool> {
        if let Self::Boolean(value) = self {
            return Some(*value);
        }
        None
    }

    #[inline]
    pub const fn identifier(&self) -> Option<PartitionedSymbol> {
        if let Self::Identifier(ident) = self {
            return Some(*ident);
        }
        None
    }

    #[inline]
    pub const fn i16(&self) -> Option<i16> {
        if let Self::I16(value) = self {
            return Some(*value);
        }
        None
    }

    pub fn in_context<'a>(&'a self, symbols: &'a PartitionedSymbolTable) -> ContextualLiteral<'a> {
        ContextualLiteral::new(symbols, self)
    }
}

impl From<bool> for Literal {
    fn from(value: bool) -> Self {
        Self::new_boolean(value)
    }
}

impl From<PartitionedSymbol> for Literal {
    fn from(value: PartitionedSymbol) -> Self {
        Self::new_identifier(value)
    }
}

impl From<i16> for Literal {
    fn from(value: i16) -> Self {
        Self::new_i16(value)
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Boolean(boolean) => write!(f, "{}", *boolean),
            Literal::I16(number) => write!(f, "{}", *number),
            Literal::Identifier(ident) => write!(f, "{}", *ident),
        }
    }
}

pub struct ContextualLiteral<'a> {
    symbols: &'a PartitionedSymbolTable,
    literal: &'a Literal,
}

impl<'a> ContextualLiteral<'a> {
    pub const fn new(symbols: &'a PartitionedSymbolTable, literal: &'a Literal) -> Self {
        Self { symbols, literal }
    }
}

impl<'a> Display for ContextualLiteral<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Literal::Identifier(symbol) = self.literal {
            write!(f, "{}", self.symbols.resolve(symbol))
        } else {
            write!(f, "{}", self.literal)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{ContextualLiteral, Literal};
    use crate::automata::partitioned_symbol_table::PartitionedSymbolTable;

    #[test]
    fn literal_identifier_resolved() {
        let symbols = PartitionedSymbolTable::new();
        let a = Literal::new_identifier(symbols.intern(0, "a"));
        let contextual_literal = ContextualLiteral::new(&symbols, &a);

        assert_eq!(contextual_literal.to_string(), "a");
    }

    #[test]
    fn test_literal_boolean() {
        let true_lit = Literal::new_true();
        let false_lit = Literal::new_false();
        assert_eq!(true_lit.to_string(), "true");
        assert_eq!(false_lit.to_string(), "false");
    }

    #[test]
    fn test_literal_i16() {
        let number = Literal::new_i16(42);
        assert_eq!(number.to_string(), "42");
    }

    #[test]
    fn test_literal_identifier_display() {
        let symbols = PartitionedSymbolTable::new();
        let symbol = symbols.intern(1, "identifier");
        let identifier_lit = Literal::new_identifier(symbol);

        assert_eq!(identifier_lit.to_string(), symbol.to_string());
    }

    #[test]
    fn test_contextual_literal_non_identifier() {
        let symbols = PartitionedSymbolTable::new();

        let number_lit = Literal::new_i16(100);
        let contextual = ContextualLiteral::new(&symbols, &number_lit);
        assert_eq!(contextual.to_string(), "100");
    }

    #[test]
    fn test_from_conversions() {
        let bool_lit: Literal = true.into();
        assert_eq!(bool_lit.to_string(), "true");

        let num_lit: Literal = 123.into();
        assert_eq!(num_lit.to_string(), "123");

        let symbols = PartitionedSymbolTable::new();
        let sym = symbols.intern(2, "sym");
        let id_lit: Literal = sym.into();

        assert_eq!(id_lit.to_string(), sym.to_string());
    }
}
