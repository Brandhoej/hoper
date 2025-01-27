use std::collections::HashSet;

use symbol_table::Symbol;

use super::{
    action::Action,
    ioa::IOA,
    location::Location,
    ta::TA,
    tioa::{LocationTree, Move, TIOA},
};

/// A specification is an automaton which is input-enabled.
/// To create a specification the TIOA must be completed to ensure that
/// at all possible states the TIOA can react to any input.
/// Intuitively it makes sense that a specification must be input-enabled
/// because any system specification should allow any interaction.
/// However, this interaction can lead to an inconsistent state.
///
/// An input cannot be precented from being sent to a system,
/// but it might be unpredictable how the system behaves after
/// receiving it. Input-enabledness enforces explicit handling
/// of all inputs at all times.
pub struct Specification(Box<dyn TIOA>);

impl Specification {
    pub fn new<T: TIOA + 'static>(tioa: T) -> Self {
        Specification(Box::new(tioa))
    }
}

impl TA for Specification {
    fn clocks(&self) -> HashSet<Symbol> {
        self.0.clocks()
    }
}

impl IOA for Specification {
    fn inputs(&self) -> HashSet<Action> {
        self.0.inputs()
    }

    fn outputs(&self) -> HashSet<Action> {
        self.0.outputs()
    }
}

impl TIOA for Specification {
    fn initial_location(&self) -> LocationTree {
        self.0.initial_location()
    }

    fn outgoing(&self, source: &LocationTree, action: Action) -> Result<Vec<Move>, ()> {
        self.0.outgoing(source, action)
    }

    fn location(&self, tree: &LocationTree) -> Result<Location, ()> {
        self.0.location(tree)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use petgraph::graph::DiGraph;
    use symbol_table::SymbolTable;

    use crate::automata::{
        action::Action, automaton::Automaton, edge::Edge, input_enabled::InputEnabled,
        literal::Literal, location::Location, statements::Statement,
    };

    #[test]
    fn test() {
        let symbols = SymbolTable::new();
        let symbol_input = symbols.intern("input");
        let symbol_a = symbols.intern("A");
        let symbol_b = symbols.intern("B");
        let mut graph = DiGraph::new();
        let node_a = graph.add_node(Location::with_name(symbol_a));
        let node_b = graph.add_node(Location::with_name(symbol_b));
        graph.add_edge(
            node_a,
            node_b,
            Edge::new_input(
                Action::new(symbol_input),
                Literal::new_true().into(),
                Statement::empty(),
            ),
        );

        let tioa = Automaton::new(node_a, graph, HashSet::new()).unwrap();
        let specification = tioa.is_input_enabled().unwrap();
    }
}
