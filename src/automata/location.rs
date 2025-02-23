use std::fmt::{self, Display, Formatter};

use itertools::Itertools;

use super::{
    expressions::Expression,
    literal::Literal,
    partitioned_symbol_table::{PartitionedSymbol, PartitionedSymbolTable},
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
        Self::Branch(locations.collect())
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
            Location::Branch(locations) => Expression::conjunctions(
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

    pub fn in_context<'a>(&'a self, symbols: &'a PartitionedSymbolTable) -> ContextualLocation<'a> {
        ContextualLocation::new(symbols, self)
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Location::Leaf { name, invariant } => write!(f, "[{}, {}]", name, invariant),
            Location::Branch(locations) => {
                if locations.is_empty() {
                    return write!(f, "()");
                }

                let join = locations.iter().map(ToString::to_string).join(",");
                write!(f, "({})", join)
            }
        }
    }
}

pub struct ContextualLocation<'a> {
    symbols: &'a PartitionedSymbolTable,
    location: &'a Location,
}

impl<'a> ContextualLocation<'a> {
    pub const fn new(symbols: &'a PartitionedSymbolTable, location: &'a Location) -> Self {
        Self { symbols, location }
    }
}

impl<'a> Display for ContextualLocation<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.location {
            Location::Leaf { name, invariant } => write!(
                f,
                "[{}, {}]",
                self.symbols.resolve(name),
                invariant.in_context(self.symbols)
            ),
            Location::Branch(locations) => {
                if locations.is_empty() {
                    return write!(f, "()");
                }

                let join = locations
                    .iter()
                    .map(|location| location.in_context(&self.symbols).to_string())
                    .join(",");
                write!(f, "({})", join)
            }
        }
    }
}
