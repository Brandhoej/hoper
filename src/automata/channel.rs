use super::action::Action;

/// A channel is used to describe the interface of an automaton in regards to
/// how the actions (or letters) are used to communicate from or to the automaton.
/// In practical terms the actions describe the buttons (inputs) and displays (outputs).
/// The buttons can be pressed by the environment and observe the inner working
/// through the displays of the automaton.
///
/// TODO: Make channels value passing but doing what Go is doing (un/-buffered)
#[derive(PartialEq, Clone, Debug)]
pub enum Channel {
    In(Action),
    Out(Action),
}

impl Channel {
    /// Creates a new input channel with an action.
    pub const fn new_in(action: Action) -> Self {
        Self::In(action)
    }

    /// Creates a new output channel with an action.
    pub const fn new_out(action: Action) -> Self {
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
}

#[cfg(test)]
mod tests {
    use crate::automata::{
        action::Action, channel::Channel, partitioned_symbol_table::PartitionedSymbolTable,
    };

    #[test]
    fn test_is_input_or_output() {
        let symbols = PartitionedSymbolTable::new();
        let a = Action::new(symbols.intern(0, "a"));
        let b = Action::new(symbols.intern(0, "b"));

        assert_ne!(a, b);

        assert!(Channel::new_in(a).is_input());
        assert!(!Channel::new_in(a).is_output());
        assert!(!Channel::new_out(a).is_input());
        assert!(Channel::new_out(a).is_output());

        assert!(Channel::new_in(b).is_input());
        assert!(!Channel::new_in(b).is_output());
        assert!(!Channel::new_out(b).is_input());
        assert!(Channel::new_out(b).is_output());
    }

    #[test]
    fn test_action() {
        let symbols = PartitionedSymbolTable::new();
        let a = Action::new(symbols.intern(0, "a"));
        let b = Action::new(symbols.intern(0, "b"));

        assert_ne!(a, b);

        assert_eq!(*Channel::new_in(a).action(), a);
        assert_eq!(*Channel::new_in(b).action(), b);
    }

    #[test]
    fn test_partial_eq() {
        let symbols = PartitionedSymbolTable::new();
        let a = Action::new(symbols.intern(0, "a"));
        let b = Action::new(symbols.intern(0, "b"));

        assert_ne!(a, b);

        assert_eq!(*Channel::new_in(a).action(), a);
        assert_eq!(*Channel::new_in(b).action(), b);

        assert_eq!(Channel::new_in(a), Channel::new_in(a));
        assert_eq!(Channel::new_in(b), Channel::new_in(b));
        assert_ne!(Channel::new_in(a), Channel::new_in(b));
        assert_ne!(Channel::new_in(b), Channel::new_in(a));

        assert_eq!(Channel::new_out(a), Channel::new_out(a));
        assert_eq!(Channel::new_out(b), Channel::new_out(b));
        assert_ne!(Channel::new_out(a), Channel::new_out(b));
        assert_ne!(Channel::new_out(b), Channel::new_out(a));

        assert_ne!(Channel::new_out(a), Channel::new_in(a));
        assert_ne!(Channel::new_out(b), Channel::new_in(b));
        assert_ne!(Channel::new_in(a), Channel::new_out(a));
        assert_ne!(Channel::new_in(b), Channel::new_out(b));
    }
}
