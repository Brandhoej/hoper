use std::fmt::Display;

use itertools::Itertools;

use petgraph::graph::NodeIndex;

use super::{action::Action, edge::Edge, ioa::IOA, location::Location, ta::TA};

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
pub struct Traversal {
    edge: Edge,
    location: LocationTree,
}

impl Traversal {
    pub const fn new(edge: Edge, location: LocationTree) -> Self {
        Self { edge, location }
    }

    pub const fn edge(&self) -> &Edge {
        &self.edge
    }

    pub const fn destination(&self) -> &LocationTree {
        &self.location
    }
}

pub trait TIOA
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

        for location in combinations.iter() {
            println!("{}", location);
        }

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
