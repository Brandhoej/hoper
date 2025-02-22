use std::collections::HashSet;

use petgraph::graph::{DiGraph, EdgeIndex, NodeIndex};

use super::{
    action::Action,
    automaton::Automaton,
    edge::Edge,
    expressions::Expression,
    literal::Literal,
    location::Location,
    partitioned_symbol_table::{PartitionedSymbol, PartitionedSymbolTable},
    statements::Statement,
};

pub struct AutomatonBuilder {
    initial: Option<NodeIndex>,
    symbols: PartitionedSymbolTable,
    graph: DiGraph<Location, Edge>,
    clocks: HashSet<PartitionedSymbol>,
}

impl AutomatonBuilder {
    pub fn new(symbols: PartitionedSymbolTable) -> Self {
        Self {
            initial: None,
            symbols: symbols,
            graph: DiGraph::new(),
            clocks: HashSet::new(),
        }
    }

    pub fn add_clock(&mut self, partition: u32, name: &str) -> PartitionedSymbol {
        let symbol = self.symbols.intern(partition, name);
        self.clocks.insert(symbol);
        symbol
    }

    pub fn add_location(&mut self, partition: u32, name: &str, invariant: Expression) -> NodeIndex {
        let symbol = self.symbols.intern(partition, name);
        let location = Location::new(symbol, invariant);
        self.graph.add_node(location)
    }

    pub fn set_initial_location(&mut self, location: NodeIndex) {
        self.initial = Some(location)
    }

    pub fn add_location_with_name(&mut self, partition: u32, name: &str) -> NodeIndex {
        self.add_location(partition, name, Literal::new_true().into())
    }

    pub fn add_edge_input(
        &mut self,
        partition: u32,
        source: NodeIndex,
        destination: NodeIndex,
        name: &str,
        mut guard: Option<Expression>,
        mut update: Option<Statement>,
    ) -> EdgeIndex {
        if guard.is_none() {
            guard = Some(Literal::new_true().into());
        }

        if update.is_none() {
            update = Some(Statement::empty());
        }

        let symbol = self.symbols.intern(partition, name);
        let action = Action::new(symbol);
        let edge = Edge::new_input(action, guard.unwrap(), update.unwrap());
        self.graph.add_edge(source, destination, edge)
    }

    pub fn add_edge_output(
        &mut self,
        partition: u32,
        source: NodeIndex,
        destination: NodeIndex,
        name: &str,
        mut guard: Option<Expression>,
        mut update: Option<Statement>,
    ) -> EdgeIndex {
        if guard.is_none() {
            guard = Some(Literal::new_true().into());
        }

        if update.is_none() {
            update = Some(Statement::empty());
        }

        let symbol = self.symbols.intern(partition, name);
        let action = Action::new(symbol);
        let edge = Edge::new_output(action, guard.unwrap(), update.unwrap());
        self.graph.add_edge(source, destination, edge)
    }

    pub fn add_loop_input(
        &mut self,
        partition: u32,
        node: NodeIndex,
        name: &str,
        guard: Option<Expression>,
        update: Option<Statement>,
    ) -> EdgeIndex {
        self.add_edge_input(partition, node, node, name, guard, update)
    }

    pub fn add_loop_output(
        &mut self,
        partition: u32,
        node: NodeIndex,
        name: &str,
        guard: Option<Expression>,
        update: Option<Statement>,
    ) -> EdgeIndex {
        self.add_edge_output(partition, node, node, name, guard, update)
    }

    pub fn build(self) -> Result<Automaton, ()> {
        if self.initial.is_none() {
            return Err(());
        }

        Automaton::new(self.initial.unwrap(), self.graph, self.clocks)
    }
}
