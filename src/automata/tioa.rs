use std::fmt::Display;

use dyn_clone::DynClone;
use itertools::Itertools;

use petgraph::graph::{EdgeIndex, NodeIndex};

use super::{channel::Channel, edge::Edge, ioa::IOA, location::Location, ta::TA};

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
pub enum LocationTree {
    Leaf(NodeIndex),
    Branch(Vec<LocationTree>),
}

impl LocationTree {
    pub const fn new_leaf(index: NodeIndex) -> Self {
        Self::Leaf(index)
    }

    pub const fn new_branch(locations: Vec<Self>) -> Self {
        Self::Branch(locations)
    }

    pub fn new_branches(
        locations: impl Iterator<Item = impl Iterator<Item = Self> + Clone>,
    ) -> impl Iterator<Item = Self> {
        locations
            .multi_cartesian_product()
            .map(|locations| Self::Branch(locations))
    }
}

impl From<NodeIndex> for LocationTree {
    fn from(value: NodeIndex) -> Self {
        LocationTree::new_leaf(value)
    }
}

impl Display for LocationTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LocationTree::Leaf(index) => write!(f, "{}", index.index()),
            LocationTree::Branch(locations) => write!(
                f,
                "({})",
                locations
                    .iter()
                    .map(|location| format!("{}", location))
                    .join(", ")
            ),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
pub enum EdgeTree {
    Identity,
    Leaf(EdgeIndex),
    Branch(Vec<EdgeTree>),
}

impl EdgeTree {
    pub const fn leaf(index: EdgeIndex) -> Self {
        Self::Leaf(index)
    }

    pub const fn branch(edges: Vec<Self>) -> Self {
        Self::Branch(edges)
    }

    pub const fn identity() -> Self {
        Self::Identity
    }

    pub const fn is_identity(&self) -> bool {
        matches!(self, EdgeTree::Identity)
    }

    pub fn branches(
        locations: impl Iterator<Item = impl Iterator<Item = Self> + Clone>,
    ) -> impl Iterator<Item = Self> {
        locations
            .multi_cartesian_product()
            .map(|locations| Self::Branch(locations))
    }
}

impl From<EdgeIndex> for EdgeTree {
    fn from(value: EdgeIndex) -> Self {
        EdgeTree::leaf(value)
    }
}

impl Display for EdgeTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EdgeTree::Leaf(index) => write!(f, "{:#?}", *index),
            EdgeTree::Branch(edges) => write!(
                f,
                "({})",
                edges
                    .iter()
                    .map(|location| format!("{}", location))
                    .join(", ")
            ),
            EdgeTree::Identity => Ok(()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Traversal {
    edge: EdgeTree,
    destination: LocationTree,
}

impl Traversal {
    pub const fn step(edge: EdgeTree, location: LocationTree) -> Self {
        Self {
            edge,
            destination: location,
        }
    }

    pub const fn stay(location: LocationTree) -> Self {
        Self::step(EdgeTree::identity(), location)
    }

    pub const fn edge(&self) -> &EdgeTree {
        &self.edge
    }

    pub const fn destination(&self) -> &LocationTree {
        &self.destination
    }

    pub fn conjoin(traversals: Vec<Traversal>) -> Traversal {
        let (locations, edges): (Vec<_>, Vec<_>) = traversals
            .into_iter()
            .map(|t| (t.destination().clone(), t.edge().clone()))
            .unzip();

        let combined_edge = match edges.as_slice() {
            [single] => single.clone(),
            _ => EdgeTree::branch(edges),
        };

        Traversal::step(combined_edge, LocationTree::new_branch(locations))
    }

    pub fn combinations(
        traversals: impl Iterator<Item = impl Iterator<Item = Self> + Clone>,
    ) -> impl Iterator<Item = Self> {
        traversals
            .multi_cartesian_product()
            .map(move |traversals| Traversal::conjoin(traversals))
    }
}

pub trait TIOA: DynClone
where
    Self: TA + IOA,
{
    fn initial_location(&self) -> LocationTree;
    fn location(&self, tree: &LocationTree) -> Result<Location, ()>;
    fn edge(&self, tree: &EdgeTree) -> Result<Edge, ()>;
    fn outgoing_traversals(
        &self,
        source: &LocationTree,
        channel: Channel,
    ) -> Result<Vec<Traversal>, ()>;
}

dyn_clone::clone_trait_object!(TIOA);

#[cfg(test)]
mod tests {
    use petgraph::graph::NodeIndex;

    use super::LocationTree;

    #[test]
    fn test_locations_combinations() {
        let zero = LocationTree::new_leaf(NodeIndex::new(0));
        let one = LocationTree::new_leaf(NodeIndex::new(1));
        let two = LocationTree::new_leaf(NodeIndex::new(2));
        let locations_a = vec![zero.clone(), one.clone(), two.clone()];
        let locations_b = vec![zero.clone(), one.clone()];
        let locations_c = vec![zero.clone(), one.clone()];
        let locations = vec![
            locations_a.into_iter(),
            locations_b.into_iter(),
            locations_c.into_iter(),
        ]
        .into_iter();
        let combinations: Vec<LocationTree> = LocationTree::new_branches(locations).collect();

        assert!(combinations.contains(&LocationTree::new_branch(vec![
            zero.clone(),
            zero.clone(),
            zero.clone()
        ])));
        assert!(combinations.contains(&LocationTree::new_branch(vec![
            zero.clone(),
            zero.clone(),
            one.clone()
        ])));

        assert!(combinations.contains(&LocationTree::new_branch(vec![
            zero.clone(),
            one.clone(),
            zero.clone()
        ])));
        assert!(combinations.contains(&LocationTree::new_branch(vec![
            zero.clone(),
            one.clone(),
            one.clone()
        ])));

        assert!(combinations.contains(&LocationTree::new_branch(vec![
            one.clone(),
            zero.clone(),
            zero.clone()
        ])));
        assert!(combinations.contains(&LocationTree::new_branch(vec![
            one.clone(),
            zero.clone(),
            one.clone()
        ])));

        assert!(combinations.contains(&LocationTree::new_branch(vec![
            one.clone(),
            one.clone(),
            zero.clone()
        ])));
        assert!(combinations.contains(&LocationTree::new_branch(vec![
            one.clone(),
            one.clone(),
            one.clone()
        ])));

        assert!(combinations.contains(&LocationTree::new_branch(vec![
            two.clone(),
            zero.clone(),
            zero.clone()
        ])));
        assert!(combinations.contains(&LocationTree::new_branch(vec![
            two.clone(),
            zero.clone(),
            one.clone()
        ])));

        assert!(combinations.contains(&LocationTree::new_branch(vec![
            two.clone(),
            one.clone(),
            zero.clone()
        ])));
        assert!(combinations.contains(&LocationTree::new_branch(vec![
            two.clone(),
            one.clone(),
            one.clone()
        ])));
        assert_eq!(combinations.len(), 12)
    }
}
