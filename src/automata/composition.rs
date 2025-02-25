use std::collections::HashSet;

use crate::zones::constraint::Clock;

use super::{
    action::Action,
    channel::Channel,
    edge::Edge,
    ioa::IOA,
    location::Location,
    partitioned_symbol_table::PartitionedSymbol,
    specification::Specification,
    ta::TA,
    tioa::{EdgeTree, LocationTree, Traversal, TIOA},
};

/// Represents the parallel composition of two timed input-output automata (TIOAs) A¹ and A².
///
/// Given two TIOAs `Aⁱ = (Locⁱ, lₒⁱ, Actⁱ, Clkⁱ, Eⁱ, Invⁱ)` where `i = 1, 2` and `Actₒ¹ ∩ Actₒ² = ∅`
/// (i.e., the output actions of each automaton do not overlap), the parallel composition `A¹ ∧ A²` is defined as a new TIOA, denoted by:
///
/// `A¹ ∧ A² = TIOA(Loc¹ × Loc², (lₒ¹, lₒ²), Act, Clk₁ ⊎ Clk₂, E, Inv)`, where:
///
/// - `Act = Act¹ ∪ Act² = Actᵢ ⊎ Actₒ`
///   - `Actᵢ = (Act¹ᵢ ∪ Act²ᵢ)` (input actions from both TIOAs)
///   - `Actₒ = Act¹ₒ ∪ Act²ₒ` (output actions from both TIOAs)
///
/// - `Clk₁ ⊎ Clk₂` represents the union of clocks from both TIOAs, ensuring synchronization across both systems.
///
/// - The invariant `Inv((l¹, l²)) = Inv¹(l¹) ∧ Inv²(l²)` holds for the composed system, ensuring that the invariant holds for each location pair from `A¹` and `A²`.
///
/// The transition relation `E` is defined as follows:
///
/// 1. **For shared actions (`a ∈ Act¹ ∩ Act²`)**:
///    - `((l¹₁, l²₁), a, φ₁ ∧ φ₂, c₁ ∪ c₂, (l¹₂, l²₂)) ∈ E` if:
///      - `(l¹₁, a, φ₁, c₁, l¹₂) ∈ E¹` (transition in `A¹`)
///      - `(l²₁, a, φ₂, c₂, l²₂) ∈ E²` (transition in `A²`)
///
/// 2. **For actions in `Act¹ \ Act²` (exclusive to A¹)**:
///    - `((l¹₁, l²), a, φ₁, c₁, (l¹₂, l²)) ∈ E` if:
///      - `(l¹₁, a, φ₁, c₁, l¹₂) ∈ E¹` (transition in `A¹`)
///      - `l² ∈ Loc²` (location from `A²`)
///
/// 3. **For actions in `Act² \ Act¹` (exclusive to A²)**:
///    - `((l¹, l²₁), a, φ₂, c₂, (l¹, l²₂)) ∈ E` if:
///      - `(l²₁, a, φ₂, c₂, l²₂) ∈ E²` (transition in `A²`)
///      - `l¹ ∈ Loc¹` (location from `A¹`)
///
/// This defines the structure of the parallel composition of two TIOAs, where actions from both automata can occur simultaneously
/// while respecting their synchronization and interaction constraints, ensuring correct coordination of both systems.
///
/// Parallel composition over multiple automata can be extended similarly, as `Aⁱ = (((A¹ ∥ A²) ∥ A³) ...)`.
#[derive(Clone)]
pub struct Composition {
    lhs: Box<Specification>,
    rhs: Box<Specification>,
    inputs: HashSet<Action>,
    outputs: HashSet<Action>,
    clocks: HashSet<PartitionedSymbol>,
    common_actions: HashSet<Action>,
    lhs_unique_actions: HashSet<Action>,
    rhs_unique_actions: HashSet<Action>,
}

impl Composition {
    pub fn new(lhs: Box<Specification>, rhs: Box<Specification>) -> Result<Self, ()> {
        // For `Clk₁ ⊎ Clk₂` to hold then they must be disjoint.
        if !lhs.clocks().is_disjoint(&rhs.clocks()) {
            return Err(());
        }

        // `Act¹ₒ ∩ Act²ₒ = ∅`
        if !lhs.outputs().is_disjoint(&rhs.outputs()) {
            return Err(());
        }

        // `Actₒ = Act¹ₒ ∪ Act²ₒ`
        let outputs: HashSet<_> = lhs.outputs().union(&rhs.outputs()).cloned().collect();

        // `Actᵢ = (Act¹ᵢ \ Act²ₒ) ∪ (Act²ᵢ \ Act¹ₒ)`
        let inputs = lhs
            .inputs()
            .difference(&rhs.outputs())
            .cloned()
            .collect::<HashSet<Action>>()
            .union(
                &rhs.inputs()
                    .difference(&lhs.outputs())
                    .cloned()
                    .collect::<HashSet<Action>>(),
            )
            .cloned()
            .collect();

        // `Act¹ \ Act²` and `Act² \ Act¹`
        let lhs_unique_actions = lhs.actions().difference(&rhs.actions()).cloned().collect();
        let rhs_unique_actions = rhs.actions().difference(&lhs.actions()).cloned().collect();

        // `a ∈ Act¹ ∩ Act²`
        let common_actions = lhs
            .actions()
            .intersection(&rhs.actions())
            .cloned()
            .collect();

        // `Clk₁ ⊎ Clk₂`
        let clocks = lhs.clocks().union(&rhs.clocks()).cloned().collect();

        Ok(Self {
            lhs,
            rhs,
            inputs,
            outputs,
            clocks,
            common_actions,
            lhs_unique_actions,
            rhs_unique_actions,
        })
    }

    pub fn channel_for(&self, action: Action) -> Result<Channel, ()> {
        if self.inputs.contains(&action) {
            Ok(Channel::new_in(action))
        } else if self.outputs.contains(&action) {
            Ok(Channel::new_out(action))
        } else {
            Err(())
        }
    }
}

impl TA for Composition {
    fn clocks(&self) -> HashSet<PartitionedSymbol> {
        self.clocks.clone()
    }

    fn clock_count(&self) -> Clock {
        self.clocks.len() as Clock
    }
}

impl IOA for Composition {
    fn inputs(&self) -> HashSet<Action> {
        self.inputs.clone()
    }

    fn outputs(&self) -> HashSet<Action> {
        self.outputs.clone()
    }
}

impl TIOA for Composition {
    fn initial_location(&self) -> LocationTree {
        LocationTree::new_branch(vec![
            self.lhs.initial_location(),
            self.rhs.initial_location(),
        ])
    }

    fn outgoing_traversals(
        &self,
        source: &LocationTree,
        action: Action,
    ) -> Result<Vec<Traversal>, ()> {
        if !self.actions().contains(&action) {
            return Err(());
        }

        if let LocationTree::Branch(sources) = source {
            if sources.len() != 2 {
                return Err(());
            }

            let lhs_location = &sources[0];
            let rhs_location = &sources[1];

            let mut lhs_traversals: Result<Vec<Traversal>, ()> = Err(());
            let mut rhs_traversals: Result<Vec<Traversal>, ()> = Err(());

            if self.common_actions.contains(&action) {
                lhs_traversals = self.lhs.outgoing_traversals(lhs_location, action);
                rhs_traversals = self.rhs.outgoing_traversals(rhs_location, action);
            } else if self.lhs_unique_actions.contains(&action) {
                lhs_traversals = self.lhs.outgoing_traversals(lhs_location, action);
                let stay = Traversal::stay(rhs_location.clone());
                rhs_traversals = Ok(vec![stay]);
            } else if self.rhs_unique_actions.contains(&action) {
                let stay = Traversal::stay(lhs_location.clone());
                lhs_traversals = Ok(vec![stay]);
                rhs_traversals = self.rhs.outgoing_traversals(rhs_location, action);
            } else {
                unreachable!()
            }

            if lhs_traversals.is_err() || rhs_traversals.is_err() {
                return Err(());
            }

            let combinations: Vec<Traversal> = Traversal::combinations(
                self.channel_for(action).unwrap(),
                vec![
                    lhs_traversals.unwrap().into_iter(),
                    rhs_traversals.unwrap().into_iter(),
                ]
                .into_iter(),
            )
            .collect();

            return Ok(combinations);
        }

        return Err(());
    }

    fn location(&self, tree: &LocationTree) -> Result<Location, ()> {
        if let LocationTree::Branch(locations) = tree {
            if locations.len() != 2 {
                return Err(());
            }

            let lhs_location = self.lhs.location(&locations[0])?;
            let rhs_location = self.rhs.location(&locations[1])?;

            return Ok(Location::combine(
                vec![lhs_location, rhs_location].into_iter(),
            ));
        }

        Err(())
    }

    fn edge(&self, tree: &EdgeTree) -> Result<Edge, ()> {
        match tree {
            EdgeTree::Branch(edges) if edges.len() == 2 => {
                if edges.len() != 2 {
                    return Err(());
                }

                let mut edge_composition: Vec<Edge> = Vec::with_capacity(2);
                let mut channel: Option<Channel> = None;

                if !edges[0].is_identity() {
                    let lhs_edge = self.lhs.edge(&edges[0])?;
                    edge_composition.push(lhs_edge.clone());
                    channel = Some(lhs_edge.channel().clone());
                }

                if !edges[1].is_identity() {
                    let rhs_edge = self.rhs.edge(&edges[1])?;
                    edge_composition.push(rhs_edge.clone());
                    channel = Some(rhs_edge.channel().clone());
                }

                return if let Some(channel) = channel {
                    Ok(Edge::conjoin(channel, edge_composition).ok().unwrap())
                } else {
                    Err(())
                };
            }
            _ => Err(()),
        }
    }
}

impl From<Composition> for Specification {
    fn from(value: Composition) -> Self {
        Self::new(value)
    }
}
