use std::fmt::Display;

use dyn_clone::DynClone;
use itertools::Itertools;

use petgraph::graph::NodeIndex;

use super::{action::Action, channel::Channel, edge::Edge, ioa::IOA, location::Location, ta::TA};

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
pub enum LocationTree {
    Leaf(NodeIndex),
    Branch(Vec<LocationTree>),
}

impl LocationTree {
    pub const fn new_leaf(node: NodeIndex) -> Self {
        Self::Leaf(node)
    }

    pub const fn new_branch(locations: Vec<Self>) -> Self {
        Self::Branch(locations)
    }

    pub fn combinations(
        locations: impl Iterator<Item = impl Iterator<Item = Self> + Clone>,
    ) -> impl Iterator<Item = Self> {
        locations
            .multi_cartesian_product()
            .map(|locations| Self::Branch(locations))
    }
}

impl Display for LocationTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LocationTree::Leaf(index) => write!(f, "{}", index.index()),
            LocationTree::Branch(locations) => write!(
                f,
                "{}",
                locations
                    .iter()
                    .map(|location| format!("{}", location))
                    .join(", ")
            ),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Traversal {
    Step {
        edge: Edge,
        destination: LocationTree,
    },
    Stay {
        location: LocationTree,
    },
}

impl Traversal {
    pub const fn step(edge: Edge, location: LocationTree) -> Self {
        Self::Step {
            edge,
            destination: location,
        }
    }

    pub const fn stay(location: LocationTree) -> Self {
        Self::Stay { location }
    }

    pub const fn edge(&self) -> Option<&Edge> {
        match self {
            Traversal::Step { edge, .. } => Some(edge),
            Traversal::Stay { .. } => None,
        }
    }

    pub const fn destination(&self) -> &LocationTree {
        match self {
            Traversal::Step {
                destination: location,
                ..
            }
            | Traversal::Stay { location } => location,
        }
    }

    pub fn conjoin(channel: Channel, traversals: Vec<Traversal>) -> Traversal {
        let locations = traversals
            .iter()
            .map(|traversal| traversal.destination().clone())
            .collect();
        let edges = traversals
            .iter()
            .filter_map(|traversal| match traversal.edge() {
                Some(edge) => Some(edge.clone()),
                None => None,
            })
            .collect();
        Traversal::step(
            Edge::conjoin(channel, edges).ok().unwrap(),
            LocationTree::new_branch(locations),
        )
    }

    pub fn combinations(
        channel: Channel,
        traversals: impl Iterator<Item = impl Iterator<Item = Self> + Clone>,
    ) -> impl Iterator<Item = Self> {
        traversals
            .multi_cartesian_product()
            .map(move |traversals| Traversal::conjoin(channel.clone(), traversals))
    }
}

pub trait TIOA: DynClone
where
    Self: TA + IOA,
{
    fn initial_location(&self) -> LocationTree;
    fn location(&self, tree: &LocationTree) -> Result<Location, ()>;
    fn outgoing_traversals(
        &self,
        source: &LocationTree,
        action: Action,
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
        let combinations: Vec<LocationTree> = LocationTree::combinations(locations).collect();

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
