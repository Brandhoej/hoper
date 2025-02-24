use std::sync::Mutex;

use dashmap::DashMap;
use petgraph::graph::{DiGraph, EdgeIndex, NodeIndex};

use super::tioa::LocationTree;

pub type ComputationTrace = Vec<(NodeIndex, EdgeIndex)>;

pub struct ComputationTree {
    locations: DashMap<LocationTree, NodeIndex>,
    graph: Mutex<DiGraph<LocationTree, EdgeIndex>>,
}

impl ComputationTree {
    pub fn new() -> Self {
        Self {
            locations: DashMap::new(),
            graph: Mutex::new(DiGraph::new()),
        }
    }

    pub fn add_node(&mut self, location: LocationTree) -> NodeIndex {
        match self.locations.entry(location.clone()) {
            dashmap::Entry::Occupied(occupied_entry) => occupied_entry.get().clone(),
            dashmap::Entry::Vacant(vacant_entry) => {
                let mut graph = self.graph.lock().unwrap();
                let index = graph.add_node(location);
                vacant_entry.insert(index);
                index
            }
        }
    }

    pub fn add_edge(&mut self, from: NodeIndex, to: NodeIndex, edge: EdgeIndex) -> EdgeIndex {
        let mut graph = self.graph.lock().unwrap();
        let index = graph.add_edge(from, to, edge);
        index
    }

    pub fn trace_to(&self, destination: NodeIndex) -> ComputationTrace {
        todo!()
    }
}
