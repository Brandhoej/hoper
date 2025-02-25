use std::{collections::HashMap, sync::Mutex};

use dashmap::{DashMap, Entry};
use petgraph::{
    dot::Dot,
    graph::{DiGraph, EdgeIndex, NodeIndex},
    Graph,
};

use super::{
    edge::{ContextualEdge, Edge},
    location::{ContextualLocation, Location},
    partitioned_symbol_table::PartitionedSymbolTable,
    tioa::{EdgeTree, LocationTree, Traversal, TIOA},
};

pub type ComputationTrace = Vec<(NodeIndex, EdgeIndex)>;

pub enum ComputationTreeNodeMark {
    Visited,  // Nodes which are fully visited.
    Frontier, // Nodes which are about to be explored.
    Error,    // Nodes which acts as a counter-example.
}

pub struct ComputationTree {
    root: NodeIndex,
    graph: Mutex<DiGraph<LocationTree, EdgeTree>>,
    markings: DashMap<NodeIndex, ComputationTreeNodeMark>,
    decorations: DashMap<NodeIndex, Vec<String>>,
}

impl ComputationTree {
    pub fn new(location: LocationTree) -> Self {
        let mut graph = DiGraph::new();
        Self {
            root: graph.add_node(location),
            graph: Mutex::new(graph),
            markings: DashMap::new(),
            decorations: DashMap::new(),
        }
    }

    pub fn root(&self) -> NodeIndex {
        self.root
    }

    pub fn enqueue(&mut self, source: NodeIndex, traversal: Traversal) -> NodeIndex {
        self.markings
            .insert(source, ComputationTreeNodeMark::Frontier);
        let mut graph = self.graph.lock().unwrap();
        let destination = graph.add_node(traversal.destination().clone());
        graph.add_edge(source, destination, traversal.edge().clone());
        destination
    }

    pub fn dequeue(&mut self, node: NodeIndex) {
        self.markings.insert(node, ComputationTreeNodeMark::Visited);
    }

    pub fn is_error(&mut self, node: NodeIndex) {
        self.markings.insert(node, ComputationTreeNodeMark::Error);
    }

    pub fn decorate(&mut self, node: NodeIndex, decoration: String) {
        self.decorations
            .entry(node)
            .or_insert_with(Vec::new)
            .push(decoration);
    }

    pub fn trace_to(&self, destination: NodeIndex) -> ComputationTrace {
        todo!()
    }

    pub fn tree_from(&self, source: NodeIndex) -> ComputationTree {
        todo!()
    }

    pub fn location(&self, index: NodeIndex) -> Option<LocationTree> {
        let graph = self.graph.lock().unwrap();
        graph.node_weight(index).cloned()
    }

    pub fn edge(&self, index: EdgeIndex) -> Option<EdgeTree> {
        let graph = self.graph.lock().unwrap();
        graph.edge_weight(index).cloned()
    }

    pub fn endpoints(&self, index: EdgeIndex) -> Option<(NodeIndex, NodeIndex)> {
        let graph = self.graph.lock().unwrap();
        graph.edge_endpoints(index)
    }

    pub fn edge_iter(&self) -> impl Iterator<Item = EdgeIndex> {
        let graph = self.graph.lock().unwrap();
        graph.edge_indices()
    }

    pub fn node_iter(&self) -> impl Iterator<Item = NodeIndex> {
        let graph = self.graph.lock().unwrap();
        graph.node_indices()
    }

    pub fn in_context<'a>(
        &'a self,
        automaton: &'a Box<dyn TIOA>,
        symbols: &'a PartitionedSymbolTable,
    ) -> ContextualComputationTree<'a> {
        ContextualComputationTree::new(automaton, symbols, self)
    }
}

pub struct ContextualComputationTree<'a> {
    automaton: &'a Box<dyn TIOA>,
    symbols: &'a PartitionedSymbolTable,
    computation_tree: &'a ComputationTree,
}

impl<'a> ContextualComputationTree<'a> {
    pub const fn new(
        automaton: &'a Box<dyn TIOA>,
        symbols: &'a PartitionedSymbolTable,
        computation_tree: &'a ComputationTree,
    ) -> Self {
        Self {
            automaton,
            symbols,
            computation_tree,
        }
    }

    pub fn graph(&self) -> Graph<ContextualLocation<'a>, ContextualEdge<'a>> {
        let mut graph = Graph::<ContextualLocation<'a>, ContextualEdge<'a>>::default();
        let mut node_map: HashMap<NodeIndex, NodeIndex> = HashMap::new();

        // Convert nodes.
        for old_index in self.computation_tree.node_iter() {
            let location_tree = self.computation_tree.location(old_index).unwrap();
            let location = self.automaton.location(&location_tree).unwrap();

            let cloned_location = Box::new(location.clone());
            let leaked_location: &'a Location = Box::leak(cloned_location);
            let contextual_location = leaked_location.in_context(&self.symbols);

            let new_index = graph.add_node(contextual_location);
            node_map.insert(old_index, new_index);
        }

        // Convert edges.
        for edge_index in self.computation_tree.edge_iter() {
            let (source_index, target_index) = self.computation_tree.endpoints(edge_index).unwrap();
            let source_new = node_map[&source_index];
            let target_new = node_map[&target_index];

            let edge_tree = self.computation_tree.edge(edge_index).unwrap();
            let edge = self.automaton.edge(&edge_tree).unwrap();
            let cloned_edge = Box::new(edge.clone());
            let leaked_edge: &'a Edge = Box::leak(cloned_edge);
            let contextual_edge = leaked_edge.in_context(&self.symbols);

            graph.add_edge(source_new, target_new, contextual_edge);
        }

        graph
    }

    pub fn dot(&self) -> String {
        let graph = self.graph();
        let binding = |graph, (node, location)| {
            let mut attributes: Vec<&str> = Vec::new();

            if let Entry::Occupied(entry) = self.computation_tree.markings.entry(node) {
                match entry.get() {
                    ComputationTreeNodeMark::Visited => {
                        attributes.push("color=green");
                    }
                    ComputationTreeNodeMark::Frontier => {
                        attributes.push("shape=box");
                    }
                    ComputationTreeNodeMark::Error => {
                        attributes.push("color=red");
                    }
                }
            }

            let mut label = String::new();
            label.push_str(format!("{}", location).as_str());

            if let Entry::Occupied(entry) = self.computation_tree.decorations.entry(node) {
                for decoration in entry.get() {
                    label.push('\n');
                    label.push_str(&decoration);
                }
            }

            let binding = format!("label=\"{}\"", label).to_string();
            attributes.push(&binding);

            attributes.join(", ")
        };
        let dot = Dot::with_attr_getters(&graph, &[], &|graph, edge| "".to_string(), &binding);
        dot.to_string()
    }
}
