use super::{
    expressions::Expression, literal::Literal, partitioned_symbol_table::PartitionedSymbol,
};

/// Locations represents sources and destinations connecting edges allowing the simulator to make moves.
#[derive(Clone, Debug)]
pub enum Location {
    /// Leaf nodes are singular entities describing an atomic source or destination for edges.
    /// They are named with a unique symbol differentiating multiple locations between eachother.
    /// Invariants describes upper-bounds on clock valuations and are restricted to An invariant
    /// must be a conjunction of simple conditions on clocks, differences between clocks, and
    /// boolean expressions not involving clocks. The bound must be given by an integer expression.
    /// Thereby, lower-bounds on clocks are disallowed and considered harmful for performance in many
    /// scenarious. Instead, if lower-bounds are strictly required then they should (Read must) be
    /// implemented as a part of all edges having the location as a destination instead.
    Leaf {
        name: PartitionedSymbol,
        invariant: Expression,
    },
    Branch(Vec<Location>),
}

impl Location {
    pub const fn new(name: PartitionedSymbol, invariant: Expression) -> Self {
        Self::Leaf { name, invariant }
    }

    pub fn combine(locations: impl Iterator<Item = Self>) -> Self {
        todo!()
    }

    pub fn with_name(name: PartitionedSymbol) -> Self {
        Self::new(name, Literal::new_true().into())
    }

    pub const fn name(&self) -> Option<&PartitionedSymbol> {
        match self {
            Location::Leaf { name, .. } => Some(name),
            Location::Branch(..) => None,
        }
    }

    pub fn invariant(&self) -> Expression {
        match self {
            Location::Leaf { invariant, .. } => invariant.clone(),
            Location::Branch(locations) => Expression::conjunction(
                locations
                    .iter()
                    .map(|location| location.invariant().clone())
                    .collect(),
            ),
        }
    }

    pub const fn is_leaf(&self) -> bool {
        matches!(self, Location::Leaf { .. })
    }
}
