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

pub struct AutomatonBuilder<'a> {
    initial: Option<NodeIndex>,
    symbols: &'a mut PartitionedSymbolTable,
    graph: DiGraph<Location, Edge>,
    clocks: HashSet<PartitionedSymbol>,
}

impl<'a> AutomatonBuilder<'a> {
    pub fn new(symbols: &'a mut PartitionedSymbolTable) -> Self {
        Self {
            initial: None,
            symbols: symbols,
            graph: DiGraph::new(),
            clocks: HashSet::new(),
        }
    }

    pub fn add_symbol(&mut self, partition: u32, string: &str) -> PartitionedSymbol {
        self.symbols.intern(partition, string)
    }

    pub fn add_clock(&mut self, partition: u32, string: &str) -> PartitionedSymbol {
        let symbol = self.add_symbol(partition, string);
        self.clocks.insert(symbol);
        symbol
    }

    pub fn add_location(
        &mut self,
        symbol: PartitionedSymbol,
        invariant: Option<Expression>,
    ) -> NodeIndex {
        let location = Location::new(symbol, invariant.unwrap_or(Literal::new_true().into()));
        self.graph.add_node(location)
    }

    pub fn set_initial_location(&mut self, location: NodeIndex) {
        self.initial = Some(location)
    }

    pub fn add_edge_input(
        &mut self,
        source: NodeIndex,
        destination: NodeIndex,
        symbol: PartitionedSymbol,
        mut guard: Option<Expression>,
        mut update: Option<Statement>,
    ) -> EdgeIndex {
        if guard.is_none() {
            guard = Some(Literal::new_true().into());
        }

        if update.is_none() {
            update = Some(Statement::empty());
        }

        let action = Action::new(symbol);
        let edge = Edge::new_input(action, guard.unwrap(), update.unwrap());
        self.graph.add_edge(source, destination, edge)
    }

    pub fn add_edge_output(
        &mut self,
        source: NodeIndex,
        destination: NodeIndex,
        symbol: PartitionedSymbol,
        mut guard: Option<Expression>,
        mut update: Option<Statement>,
    ) -> EdgeIndex {
        if guard.is_none() {
            guard = Some(Literal::new_true().into());
        }

        if update.is_none() {
            update = Some(Statement::empty());
        }

        let action = Action::new(symbol);
        let edge = Edge::new_output(action, guard.unwrap(), update.unwrap());
        self.graph.add_edge(source, destination, edge)
    }

    pub fn build(self) -> Result<Automaton, ()> {
        if self.initial.is_none() {
            return Err(());
        }

        Automaton::new(self.initial.unwrap(), self.graph, self.clocks)
    }
}
