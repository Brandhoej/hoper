use super::partitioned_symbol_table::PartitionedSymbol;

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
