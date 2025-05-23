use std::fmt::{self, Display};

use super::{action::Action, partitioned_symbol_table::PartitionedSymbolTable};

/// A channel is used to describe the interface of an automaton in regards to
/// how the actions (or letters) are used to communicate from or to the automaton.
/// In practical terms the actions describe the buttons (inputs) and displays (outputs).
/// The buttons can be pressed by the environment and observe the inner working
/// through the displays of the automaton.
///
/// TODO: Make channels value passing but doing what Go is doing (un/-buffered)
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
pub enum Channel {
    In(Action),
    Out(Action),
}

impl Channel {
    /// Creates a new input channel with an action.
    pub const fn new_input(action: Action) -> Self {
        Self::In(action)
    }

    /// Creates a new output channel with an action.
    pub const fn new_output(action: Action) -> Self {
        Self::Out(action)
    }

    /// Returns the action (or letter) the channel communicates with.
    pub const fn action(&self) -> &Action {
        match self {
            Channel::In(action) | Channel::Out(action) => action,
        }
    }

    /// Returns true if the channel is an input.
    pub const fn is_input(&self) -> bool {
        matches!(self, Channel::In(_))
    }

    /// Returns true if the channel is an output.
    pub const fn is_output(&self) -> bool {
        matches!(self, Channel::Out(_))
    }

    pub fn in_context<'a>(&'a self, symbols: &'a PartitionedSymbolTable) -> ContextualChannel<'a> {
        ContextualChannel::new(symbols, self)
    }
}

pub struct ContextualChannel<'a> {
    symbols: &'a PartitionedSymbolTable,
    channel: &'a Channel,
}

impl<'a> ContextualChannel<'a> {
    pub const fn new(symbols: &'a PartitionedSymbolTable, channel: &'a Channel) -> Self {
        Self { symbols, channel }
    }
}

impl<'a> Display for ContextualChannel<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.channel {
            Channel::In(action) => write!(f, "{}?", self.symbols.resolve(action.letter())),
            Channel::Out(action) => write!(f, "{}!", self.symbols.resolve(action.letter())),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{HashMap, HashSet};

    use crate::automata::{
        action::Action, channel::Channel, partitioned_symbol_table::PartitionedSymbolTable,
    };

    #[test]
    fn test_is_input_or_output() {
        let symbols = PartitionedSymbolTable::new();
        let a = Action::new(symbols.intern(0, "a"));
        let b = Action::new(symbols.intern(0, "b"));

        assert_ne!(a, b);

        assert!(Channel::new_input(a).is_input());
        assert!(!Channel::new_input(a).is_output());
        assert!(!Channel::new_output(a).is_input());
        assert!(Channel::new_output(a).is_output());

        assert!(Channel::new_input(b).is_input());
        assert!(!Channel::new_input(b).is_output());
        assert!(!Channel::new_output(b).is_input());
        assert!(Channel::new_output(b).is_output());
    }

    #[test]
    fn test_action() {
        let symbols = PartitionedSymbolTable::new();
        let a = Action::new(symbols.intern(0, "a"));
        let b = Action::new(symbols.intern(0, "b"));

        assert_ne!(a, b);

        assert_eq!(*Channel::new_input(a).action(), a);
        assert_eq!(*Channel::new_input(b).action(), b);
    }

    #[test]
    fn test_partial_eq() {
        let symbols = PartitionedSymbolTable::new();
        let a = Action::new(symbols.intern(0, "a"));
        let b = Action::new(symbols.intern(0, "b"));

        assert_ne!(a, b);

        assert_eq!(*Channel::new_input(a).action(), a);
        assert_eq!(*Channel::new_input(b).action(), b);

        assert_eq!(Channel::new_input(a), Channel::new_input(a));
        assert_eq!(Channel::new_input(b), Channel::new_input(b));
        assert_ne!(Channel::new_input(a), Channel::new_input(b));
        assert_ne!(Channel::new_input(b), Channel::new_input(a));

        assert_eq!(Channel::new_output(a), Channel::new_output(a));
        assert_eq!(Channel::new_output(b), Channel::new_output(b));
        assert_ne!(Channel::new_output(a), Channel::new_output(b));
        assert_ne!(Channel::new_output(b), Channel::new_output(a));

        assert_ne!(Channel::new_output(a), Channel::new_input(a));
        assert_ne!(Channel::new_output(b), Channel::new_input(b));
        assert_ne!(Channel::new_input(a), Channel::new_output(a));
        assert_ne!(Channel::new_input(b), Channel::new_output(b));
    }

    #[test]
    fn test_contains() {
        let symbols = PartitionedSymbolTable::new();
        let a = Action::new(symbols.intern(0, "a"));
        let b = Action::new(symbols.intern(0, "b"));
        let c = Action::new(symbols.intern(0, "c"));
        let d = Action::new(symbols.intern(0, "d"));

        assert!(vec![a, b, c].contains(&a));
        assert!(vec![a, b, c].contains(&b));
        assert!(vec![a, b, c].contains(&c));
        assert!(!vec![a, b, c].contains(&d));

        let mut hashset = HashSet::new();
        hashset.insert(a);
        hashset.insert(b);
        assert!(hashset.contains(&a));
        assert!(hashset.contains(&b));
        assert!(!hashset.contains(&c));
        assert!(!hashset.contains(&d));
    }
}
