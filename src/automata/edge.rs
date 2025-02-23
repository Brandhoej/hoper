use std::fmt::{self, Display, Formatter};

use super::{
    action::Action, channel::Channel, expressions::Expression,
    partitioned_symbol_table::PartitionedSymbolTable, statements::Statement,
};

/// Represents a symbolic transition for an automaton. Intuitively this means that an edge
/// represents a set of transitions. The edge is either an input or output depending on
/// its channel. For the edge to be traversable the guard must be satisfied. For all states
/// satisfying the guard the update can be apply simulating the traversal yielding a resulting state.
#[derive(Clone, Debug)]
pub struct Edge {
    channel: Channel,
    /// A guard must be a conjunction of simple conditions on clocks,
    /// differences between clocks, and boolean expressions not involving clocks.
    /// Ultimately it should be impossible to construct a convex federation.
    guard: Expression,
    update: Statement,
}

impl Edge {
    /// Creates a new edge which is either rinput or output depending on the channel.
    /// It is guarded by a boolean expression which must be satisfied for it to be enabled.
    /// When the edge is traversed the update is executed on the state yielding a new state.
    pub const fn new(channel: Channel, guard: Expression, update: Statement) -> Self {
        Self {
            channel,
            guard,
            update,
        }
    }

    /// Creates a new edge with an input channel for the action.
    /// It is guarded by a boolean expression which must be satisfied for it to be enabled.
    /// When the edge is traversed the update is executed on the state yielding a new state.
    pub const fn new_input(action: Action, guard: Expression, update: Statement) -> Self {
        Edge::new(Channel::In(action), guard, update)
    }

    /// Creates a new edge with an output channel for the action.
    /// It is guarded by a boolean expression which must be satisfied for it to be enabled.
    /// When the edge is traversed the update is executed on the state yielding a new state.
    pub const fn new_output(action: Action, guard: Expression, update: Statement) -> Self {
        Edge::new(Channel::Out(action), guard, update)
    }

    /// Creates a conjoined edge from all the edges where the guard is a conjunction and the updates
    /// are a parallel construction of all edge updates.
    pub fn conjoin(channel: Channel, edges: Vec<Self>) -> Result<Self, ()> {
        // We cannot conjoin zero edges together.
        if edges.is_empty() {
            return Err(());
        }

        let (guards, updates) =
            edges
                .into_iter()
                .fold((Vec::new(), Vec::new()), |(mut guards, mut updates), m| {
                    guards.push(m.guard);
                    updates.push(m.update);
                    (guards, updates)
                });

        // Here the combination of guards and edges adhering to the semantics is constructed.
        // Guards are just conjoined meaning all the guards from all edges must be sat for the conjoined edge to be enabled.
        // Updates are by definition disjoint meaning that computing them in any order will produce the same new state.
        // For this reason we wrap the updates in a branch which communicates that is can be computed in parallel.
        // However, by definition, the updates can be any sequence combining exactly all the updates once in some way.
        let guard = Expression::conjunctions(guards);
        let update = Statement::branch(updates);

        Ok(Self::new(channel, guard, update))
    }

    /// Returns the channel of the guard.
    pub const fn channel(&self) -> &Channel {
        &self.channel
    }

    /// Returns the action of the guard's channel.
    pub const fn action(&self) -> &Action {
        self.channel().action()
    }

    /// Returns true if the edge has an input channel.
    pub const fn is_input(&self) -> bool {
        self.channel().is_input()
    }

    /// Returns true if the edge has an output channel.
    pub const fn is_output(&self) -> bool {
        self.channel().is_output()
    }

    /// Returns the guard of the edge.
    pub const fn guard(&self) -> &Expression {
        &self.guard
    }

    /// Returns the update of the edge.
    pub const fn update(&self) -> &Statement {
        &self.update
    }

    pub fn in_context<'a>(&'a self, symbols: &'a PartitionedSymbolTable) -> ContextualEdge<'a> {
        ContextualEdge::new(symbols, self)
    }
}

impl Display for Edge {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[{} {} {}]", self.guard(), self.action(), self.update())
    }
}

pub struct ContextualEdge<'a> {
    symbols: &'a PartitionedSymbolTable,
    edge: &'a Edge,
}

impl<'a> ContextualEdge<'a> {
    pub const fn new(symbols: &'a PartitionedSymbolTable, edge: &'a Edge) -> Self {
        Self { symbols, edge }
    }
}

impl<'a> Display for ContextualEdge<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}\n{}\n{}",
            self.edge.guard().in_context(self.symbols),
            self.edge.channel().in_context(self.symbols),
            self.edge.update().in_context(self.symbols)
        )
    }
}
