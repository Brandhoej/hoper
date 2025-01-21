use std::collections::HashSet;

use symbol_table::Symbol;

use crate::zones::constraint::Clock;

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
pub struct Specification(dyn TIOA);

impl TA for Specification {
    fn clocks(&self) -> Clock {
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
    use petgraph::graph::DiGraph;
    use symbol_table::SymbolTable;

    use crate::automata::{
        action::Action, automaton::Automaton, completer::Completer, edge::Edge,
        expressions::Expression, location::Location, statements::Statement,
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
                Expression::new_true(),
                Statement::empty(),
            ),
        );

        let tioa = Automaton::new(node_a, graph).unwrap();
        let specification = tioa.complete();
    }
}
