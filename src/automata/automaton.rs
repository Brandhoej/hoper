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
    tioa::{LocationTree, Move, TIOA},
};

#[derive(Clone)]
pub struct Automaton {
    initial: NodeIndex,
    graph: DiGraph<Location, Edge>,
    inputs: HashSet<Action>,
    outputs: HashSet<Action>,
}

impl Automaton {
    pub fn new(initial: NodeIndex, graph: DiGraph<Location, Edge>) -> Result<Self, ()> {
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

    pub fn edge(&self, index: EdgeIndex) -> Option<&Edge> {
        self.graph.edge_weight(index)
    }

    pub fn inputs(&self) -> impl Iterator<Item = &Action> {
        self.inputs.iter()
    }

    pub fn outputs(&self) -> impl Iterator<Item = &Action> {
        self.outputs.iter()
    }

    pub fn moves<'a, T: Iterator<Item = EdgeReference<'a, Edge>> + 'a>(
        &'a self,
        edges: T,
    ) -> impl Iterator<Item = Move> + use<'a, T> {
        edges.map(|edge| Move::to(edge.weight().clone(), LocationTree::new_leaf(edge.target())))
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
}

impl TA for Automaton {
    fn clocks(&self) -> Clock {
        todo!()
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

    fn outgoing(&self, source: &LocationTree, action: Action) -> Result<Vec<Move>, ()> {
        if let LocationTree::Leaf(node) = source {
            Ok(self
                .moves(self.filter_by_action(self.outgoing(*node), action))
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
    use petgraph::graph::DiGraph;
    use symbol_table::SymbolTable;

    use crate::automata::{expressions::Expression, statements::Statement};

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
                Expression::new_true(),
                Statement::empty(),
            ),
        );

        let tioa = Automaton::new(node_a, graph).unwrap();
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
