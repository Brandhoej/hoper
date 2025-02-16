use std::collections::HashSet;

use petgraph::{
    graph::{DiGraph, EdgeIndex, EdgeReference, NodeIndex},
    visit::EdgeRef,
    Direction::{Incoming, Outgoing},
};
use symbol_table::Symbol;

use crate::zones::constraint::Clock;

use super::{
    action::Action,
    channel::Channel,
    edge::Edge,
    ioa::IOA,
    location::Location,
    ta::TA,
    tioa::{LocationTree, Traversal, TIOA},
};

/// A Timed Input/Output Automaton which describes real time behaviour using clocks over reals.
/// The underlying datastructure is a directed graph connecting locations through edges. This
/// structure allows a symbolic representation of a TIOTS.
#[derive(Clone, Debug)]
pub struct Automaton {
    initial: NodeIndex,
    graph: DiGraph<Location, Edge>,
    clocks: HashSet<Symbol>,
    inputs: HashSet<Action>,
    outputs: HashSet<Action>,
}

impl Automaton {
    pub fn new(
        initial: NodeIndex,
        graph: DiGraph<Location, Edge>,
        clocks: HashSet<Symbol>,
    ) -> Result<Self, ()> {
        let mut inputs = HashSet::new();
        let mut outputs = HashSet::new();

        for edge in graph.edge_weights() {
            match edge.channel() {
                Channel::In(action) => inputs.insert(*action),
                Channel::Out(action) => outputs.insert(*action),
            };
        }

        if !inputs.is_disjoint(&outputs) {
            return Err(());
        }

        Ok(Self {
            initial,
            graph,
            clocks,
            inputs,
            outputs,
        })
    }

    pub fn initial(&self) -> NodeIndex {
        self.initial
    }

    pub fn location(&self, index: NodeIndex) -> Option<&Location> {
        self.graph.node_weight(index)
    }

    pub fn location_tree(&self, index: NodeIndex) -> LocationTree {
        LocationTree::new_leaf(index)
    }

    pub fn edge(&self, index: EdgeIndex) -> Option<&Edge> {
        self.graph.edge_weight(index)
    }

    pub fn inputs(&self) -> impl Iterator<Item = &Action> {
        self.inputs.iter()
    }

    pub fn outputs(&self) -> impl Iterator<Item = &Action> {
        self.outputs.iter()
    }

    pub fn traversals<'a, T: Iterator<Item = EdgeReference<'a, Edge>> + 'a>(
        &'a self,
        edges: T,
    ) -> impl Iterator<Item = Traversal> + use<'a, T> {
        edges.map(|edge| Traversal::step(edge.weight().clone(), self.location_tree(edge.target())))
    }

    pub fn edges<'a, T: Iterator<Item = EdgeReference<'a, Edge>> + 'a>(
        &'a self,
        edges: T,
    ) -> impl Iterator<Item = &'a Edge> + use<'a, T> {
        edges.map(|edge| edge.weight())
    }

    pub fn ingoing(&self, node: NodeIndex) -> impl Iterator<Item = EdgeReference<Edge>> {
        self.graph.edges_directed(node, Incoming)
    }

    pub fn outgoing(&self, node: NodeIndex) -> impl Iterator<Item = EdgeReference<Edge>> {
        self.graph.edges_directed(node, Outgoing)
    }

    pub fn out_degree(&self, node: NodeIndex) -> usize {
        self.outgoing(node).count()
    }

    pub fn in_degree(&self, node: NodeIndex) -> usize {
        self.ingoing(node).count()
    }

    pub fn filter_by_channel<'a>(
        &'a self,
        edges: impl Iterator<Item = EdgeReference<'a, Edge>> + 'a,
        target: Channel,
    ) -> impl Iterator<Item = EdgeReference<'a, Edge>> {
        edges.filter(move |reference| *reference.weight().channel() == target)
    }

    pub fn filter_by_input<'a>(
        &'a self,
        edges: impl Iterator<Item = EdgeReference<'a, Edge>> + 'a,
    ) -> impl Iterator<Item = EdgeReference<'a, Edge>> {
        edges.filter(move |reference| reference.weight().is_input())
    }

    pub fn filter_by_output<'a>(
        &'a self,
        edges: impl Iterator<Item = EdgeReference<'a, Edge>> + 'a,
    ) -> impl Iterator<Item = EdgeReference<'a, Edge>> {
        edges.filter(move |reference| reference.weight().is_output())
    }

    pub fn filter_by_action<'a>(
        &'a self,
        edges: impl Iterator<Item = EdgeReference<'a, Edge>> + 'a,
        target: Action,
    ) -> impl Iterator<Item = EdgeReference<'a, Edge>> {
        edges.filter(move |reference| match reference.weight().channel() {
            Channel::In(action) | Channel::Out(action) => *action == target,
        })
    }

    pub fn filter_by_action_id<'a>(
        &'a self,
        edges: impl Iterator<Item = EdgeReference<'a, Edge>> + 'a,
        letter: Symbol,
    ) -> impl Iterator<Item = EdgeReference<'a, Edge>> {
        edges.filter(move |reference| match reference.weight().channel() {
            Channel::In(action) | Channel::Out(action) => *action.letter() == letter,
        })
    }

    pub fn connecting(
        &self,
        source: NodeIndex,
        destination: NodeIndex,
    ) -> impl Iterator<Item = EdgeReference<Edge>> {
        self.graph.edges_connecting(source, destination).into_iter()
    }

    pub fn connecting_degree(&self, source: NodeIndex, destination: NodeIndex) -> usize {
        self.connecting(source, destination).count()
    }

    pub fn edge_iter(&self) -> impl Iterator<Item = EdgeIndex> {
        self.graph.edge_indices()
    }

    pub fn node_iter(&self) -> impl Iterator<Item = NodeIndex> {
        self.graph.node_indices()
    }

    pub fn order(&self) -> usize {
        self.graph.node_count()
    }

    /// Adds an edge to the underlying graph without ensuring that adding the edge breaks any
    /// of the rules of the Automaton. An example is non-determinism, where an existing edge
    /// can lead to a different state from the same state as the edge to be added. Ergo, this
    /// functionality should be used with extreme caution.
    pub fn force_add_edge(
        &mut self,
        source: NodeIndex,
        edge: Edge,
        destination: NodeIndex,
    ) -> EdgeIndex {
        self.graph.add_edge(source, destination, edge)
    }
}

impl TA for Automaton {
    fn clocks(&self) -> HashSet<Symbol> {
        self.clocks.clone()
    }

    fn clock_count(&self) -> Clock {
        self.clocks.len() as Clock
    }
}

impl IOA for Automaton {
    fn inputs(&self) -> HashSet<Action> {
        self.inputs.clone()
    }

    fn outputs(&self) -> HashSet<Action> {
        self.outputs.clone()
    }
}

impl TIOA for Automaton {
    fn initial_location(&self) -> LocationTree {
        LocationTree::Leaf(self.initial)
    }

    fn outgoing_traversals(
        &self,
        source: &LocationTree,
        action: Action,
    ) -> Result<Vec<Traversal>, ()> {
        if let LocationTree::Leaf(node) = source {
            Ok(self
                .traversals(self.filter_by_action(self.outgoing(*node), action))
                .collect())
        } else {
            Err(())
        }
    }

    fn location(&self, tree: &LocationTree) -> Result<Location, ()> {
        if let LocationTree::Leaf(index) = tree {
            return match self.location(*index) {
                Some(location) => Ok(location.clone()),
                None => Err(()),
            };
        }

        Err(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use petgraph::graph::DiGraph;
    use symbol_table::SymbolTable;

    use crate::automata::{literal::Literal, statements::Statement};

    use super::{Action, Automaton, Edge, Location};

    #[test]
    fn test_simple_tioa() {
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
        assert_eq!(tioa.initial(), node_a);

        assert_eq!(tioa.in_degree(node_a), 0);
        assert_eq!(tioa.out_degree(node_a), 1);
        assert_eq!(tioa.connecting_degree(node_a, node_b), 1);
        assert_eq!(
            tioa.filter_by_input(tioa.connecting(node_a, node_b))
                .count(),
            1
        );

        assert_eq!(tioa.in_degree(node_b), 1);
        assert_eq!(tioa.out_degree(node_b), 0);
        assert_eq!(tioa.connecting_degree(node_b, node_a), 0);

        assert_eq!(
            tioa.filter_by_action_id(tioa.outgoing(node_a), symbol_input)
                .count(),
            1
        );
    }
}
