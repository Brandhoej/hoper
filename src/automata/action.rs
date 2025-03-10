use std::fmt::{self, Display};

use super::{
    channel::Channel,
    expressions::Expression,
    partitioned_symbol_table::{PartitionedSymbol, PartitionedSymbolTable},
};

/// An action is a letter from an alphabet of all actions.
/// Inherently these are not partitioned in input/outputs instead
/// the actions allows for the same letter to be used in multiple
/// channel instances whilst still being uniquely identifiable.
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub struct Action {
    letter: PartitionedSymbol,
}

impl Action {
    /// Constructs a new action for the provided letter.
    pub const fn new(letter: PartitionedSymbol) -> Self {
        Self { letter }
    }

    // Returns the letter of the action which uniquely differentiates it.
    pub const fn letter(&self) -> &PartitionedSymbol {
        &self.letter
    }

    pub fn in_context<'a>(&'a self, symbols: &'a PartitionedSymbolTable) -> ContextualAction<'a> {
        ContextualAction::new(symbols, self)
    }

    pub fn input(self) -> Channel {
        Channel::new_input(self)
    }

    pub fn output(self) -> Channel {
        Channel::new_output(self)
    }
}

impl Display for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.letter)
    }
}

pub struct ContextualAction<'a> {
    symbols: &'a PartitionedSymbolTable,
    action: &'a Action,
}

impl<'a> ContextualAction<'a> {
    pub const fn new(symbols: &'a PartitionedSymbolTable, action: &'a Action) -> Self {
        Self { symbols, action }
    }
}

impl<'a> Display for ContextualAction<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.symbols.resolve(self.action.letter()))
    }
}

#[cfg(test)]
mod tests {
    use crate::automata::{action::Action, partitioned_symbol_table::PartitionedSymbolTable};

    #[test]
    fn test_partial_eq() {
        let symbols = PartitionedSymbolTable::new();
        let a = Action::new(symbols.intern(0, "a"));
        let b = Action::new(symbols.intern(0, "b"));

        assert_eq!(a, a);
        assert_eq!(b, b);
        assert_ne!(a, b);
    }

    #[test]
    fn test_letter() {
        let symbols = PartitionedSymbolTable::new();
        let a0 = Action::new(symbols.intern(0, "a"));
        let a1 = Action::new(symbols.intern(0, "a"));
        let b = Action::new(symbols.intern(0, "b"));

        assert_eq!(a0.letter(), a0.letter());
        assert_eq!(b.letter(), b.letter());
        assert_ne!(a0.letter(), b.letter());

        assert_eq!(a1.letter(), a1.letter());
        assert_eq!(b.letter(), b.letter());
        assert_ne!(a1.letter(), b.letter());
    }
}
