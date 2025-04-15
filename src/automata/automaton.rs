use std::collections::{HashMap, HashSet, VecDeque};

use itertools::Itertools;
use petgraph::{
    dot::Dot,
    graph::{DiGraph, EdgeIndex, EdgeReference, NodeIndex},
    visit::{EdgeRef, IntoNodeReferences},
    Direction::{Incoming, Outgoing},
    Graph,
};

use crate::zones::constraint::Clock;

use super::{
    action::Action,
    channel::Channel,
    edge::{ContextualEdge, Edge},
    ioa::IOA,
    location::{ContextualLocation, Location},
    partitioned_symbol_table::{PartitionedSymbol, PartitionedSymbolTable},
    ta::TA,
    tioa::{EdgeTree, LocationTree, Traversal, TIOA},
};

/// A Timed Input/Output Automaton which describes real time behaviour using clocks over reals.
/// The underlying datastructure is a directed graph connecting locations through edges. This
/// structure allows a symbolic representation of a TIOTS.
#[derive(Clone, Debug)]
pub struct Automaton {
    initial: NodeIndex,
    graph: DiGraph<Location, Edge>,
    clocks: HashSet<PartitionedSymbol>,
    inputs: HashSet<Action>,
    outputs: HashSet<Action>,
}

impl Automaton {
    pub fn new(
        initial: NodeIndex,
        graph: DiGraph<Location, Edge>,
        clocks: HashSet<PartitionedSymbol>,
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

    pub fn edge(&self, index: EdgeIndex) -> Option<&Edge> {
        self.graph.edge_weight(index)
    }

    pub fn inputs(&self) -> impl Iterator<Item = &Action> {
        self.inputs.iter()
    }

    pub fn outputs(&self) -> impl Iterator<Item = &Action> {
        self.outputs.iter()
    }

    pub fn node_index_of(&self, symbols: Vec<PartitionedSymbol>) -> Option<NodeIndex> {
        self.graph.node_references()
            .find(|(_, location)| location.fullname().eq(&symbols))
            .map(|(index, _)| index)
    }

    pub fn traversals<'a, T: Iterator<Item = EdgeReference<'a, Edge>> + 'a>(
        &'a self,
        edges: T,
    ) -> impl Iterator<Item = Traversal> + use<'a, T> {
        edges.map(|edge| Traversal::step(EdgeTree::leaf(edge.id()), edge.target().into()))
    }

    pub fn edges<'a, T: Iterator<Item = EdgeReference<'a, Edge>> + 'a>(
        &'a self,
        edges: T,
    ) -> impl Iterator<Item = &'a Edge> + use<'a, T> {
        edges.map(|edge| edge.weight())
    }

    pub fn all_edges(&self) -> impl Iterator<Item = EdgeReference<Edge>> {
        self.graph.edge_references()
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
        letter: PartitionedSymbol,
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

    pub fn in_context<'a>(
        &'a self,
        symbols: &'a PartitionedSymbolTable,
    ) -> ContextualAutomaton<'a> {
        ContextualAutomaton::new(symbols, self)
    }
}

impl TA for Automaton {
    fn clocks(&self) -> HashSet<PartitionedSymbol> {
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
        channel: Channel,
    ) -> Result<Vec<Traversal>, ()> {
        if let LocationTree::Leaf(node) = source {
            Ok(self
                .traversals(self.filter_by_channel(self.outgoing(*node), channel))
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

    fn edge(&self, tree: &EdgeTree) -> Result<Edge, ()> {
        if let EdgeTree::Leaf(index) = tree {
            return match self.edge(*index) {
                Some(edge) => Ok(edge.clone()),
                None => Err(()),
            };
        }

        Err(())
    }
}

pub trait IntoAutomaton {
    fn into_automaton(self) -> Result<Automaton, ()>;
}

impl<T: TIOA> IntoAutomaton for T {
    fn into_automaton(self) -> Result<Automaton, ()> {
        let mut graph: Graph<Location, Edge> = DiGraph::new();
        let mut mapping: HashMap<LocationTree, NodeIndex> = HashMap::new();
        let mut visited: HashSet<LocationTree> = HashSet::new();
        let mut trees: VecDeque<LocationTree> = VecDeque::new();

        trees.push_back(self.initial_location());

        while let Some(source_tree) = trees.pop_front() {
            if !visited.insert(source_tree.clone()) {
                continue;
            }

            let from = self.location(&source_tree).unwrap();

            let source = *mapping
                .entry(source_tree.clone())
                .or_insert_with(|| graph.add_node(from));

            for channel in self.channels() {
                let traversals = self.outgoing_traversals(&source_tree, channel).unwrap();
                for traversal in traversals {
                    let destination_tree = traversal.destination().clone();
                    let to = self.location(&destination_tree).unwrap();
                    let destination = *mapping
                        .entry(destination_tree.clone())
                        .or_insert_with(|| graph.add_node(to));
                    let edge_tree = traversal.edge();
                    let edge = self.edge(edge_tree).unwrap();
                    graph.add_edge(source, destination, edge);
                    trees.push_back(destination_tree);
                }
            }
        }

        let initial = *mapping.get(&self.initial_location()).unwrap();

        Automaton::new(initial, graph, self.clocks())
    }
}

pub struct ContextualAutomaton<'a> {
    symbols: &'a PartitionedSymbolTable,
    automaton: &'a Automaton,
}

impl<'a> ContextualAutomaton<'a> {
    pub const fn new(symbols: &'a PartitionedSymbolTable, automaton: &'a Automaton) -> Self {
        Self { symbols, automaton }
    }

    pub fn graph(&self) -> Graph<ContextualLocation<'a>, ContextualEdge<'a>> {
        let mut graph = Graph::<ContextualLocation<'a>, ContextualEdge<'a>>::default();
        let mut node_map: HashMap<NodeIndex, NodeIndex> = HashMap::new();

        // Convert nodes.
        for old_node in self.automaton.node_iter() {
            let location = self.automaton.location(old_node).unwrap();
            let contextual_location = location.in_context(&self.symbols);
            let new_node = graph.add_node(contextual_location);
            node_map.insert(old_node, new_node);
        }

        // Convert edges.
        for edge in self.automaton.all_edges() {
            let source_new = node_map[&edge.source()];
            let target_new = node_map[&edge.target()];
            let contextual_edge = edge.weight().in_context(&self.symbols);
            graph.add_edge(source_new, target_new, contextual_edge);
        }

        graph
    }

    pub fn dot(&self) -> String {
        let graph = self.graph();
        let binding = vec![];
        let dot = Dot::with_config(&graph, &binding);
        dot.to_string()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use petgraph::graph::DiGraph;

    use crate::automata::{
        literal::Literal, partitioned_symbol_table::PartitionedSymbolTable, statements::Statement,
    };

    use super::{Action, Automaton, Edge, Location};

    #[test]
    fn test_simple_tioa() {
        let symbols = PartitionedSymbolTable::new();
        let symbol_input = symbols.intern(0, "input");
        let symbol_a = symbols.intern(0, "A");
        let symbol_b = symbols.intern(0, "B");
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
