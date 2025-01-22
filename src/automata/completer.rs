use super::{automaton::Automaton, specification::Specification};

pub trait Completer {
    fn complete(self) -> Box<Specification>;
}

impl Completer for Automaton {
    fn complete(self) -> Box<Specification> {
        Box::new(Specification::new(self))
    }
}
