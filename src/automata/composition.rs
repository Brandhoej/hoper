use std::collections::HashSet;


use crate::{
    sets::{are_disjoint, intersection, skip_nth, subtract, union},
    zones::constraint::Clock,
};

use super::{
    action::Action,
    ioa::IOA,
    location::Location,
    partitioned_symbol_table::PartitionedSymbol,
    specification::Specification,
    ta::TA,
    tioa::{LocationTree, Traversal, TIOA},
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
pub struct Composition {
    specifications: Vec<Box<Specification>>,
    inputs: HashSet<Action>,
    outputs: HashSet<Action>,
    clocks: HashSet<PartitionedSymbol>,
    unique_actions: Vec<HashSet<Action>>,
    common_actions: HashSet<Action>,
}

impl Composition {
    pub fn new(tioas: Vec<Box<Specification>>) -> Result<Self, ()> {
        if tioas.len() < 2 {
            return Err(());
        }

        let all_outputs = tioas.iter().map(|tioa| tioa.outputs());
        let all_inputs = tioas.iter().map(|tioa| tioa.inputs());
        let all_actions = tioas.iter().map(|tioa| tioa.actions());
        let all_clocks = tioas.iter().map(|tioa| tioa.clocks());

        // For `Clk₁ ⊎ Clk₂` to hold then they must be disjoint.
        if !are_disjoint(&all_clocks) {
            return Err(());
        }

        // `Act¹ₒ ∩ Act²ₒ = ∅`
        if !are_disjoint(&all_outputs) {
            return Err(());
        }

        // `Actₒ = Act¹ₒ ∪ Act²ₒ`
        let outputs = union(all_outputs.clone()).collect();

        // `Actᵢ = (Act¹ᵢ \ Act²ₒ) ∪ (Act²ᵢ \ Act¹ₒ)`
        let inputs = union(
            all_inputs
                .clone()
                .map(|inputs| subtract(inputs, &outputs))
                .map(HashSet::from_iter),
        )
        .collect();

        // `Act¹ \ Act²` and `Act² \ Act¹`
        let unique_actions = all_actions
            .clone()
            .enumerate()
            .map(|(i, actions)| {
                let exclusive_union = union(skip_nth(all_actions.clone(), i)).collect();
                subtract(actions, &exclusive_union).collect()
            })
            .collect();

        // `a ∈ Act¹ ∩ Act²`
        let common_actions = intersection(all_actions).collect();

        // `Clk₁ ⊎ Clk₂`
        let clocks = union(all_clocks).collect();

        Ok(Self {
            specifications: tioas,
            inputs,
            outputs,
            clocks,
            unique_actions,
            common_actions,
        })
    }

    pub fn size(&self) -> usize {
        self.specifications.len()
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
        LocationTree::new_branch(
            self.specifications
                .iter()
                .map(|tioa| tioa.initial_location())
                .collect(),
        )
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
            // It is a common action between all aggregate systems.
            // Therefore, the transition happens for all simultaneously.
            if self.common_actions.contains(&action) {
                // Retrieve all the outgoing traversals which is avaiable in the underlying specifications.
                let mut traversals = Vec::with_capacity(self.specifications.len());
                for (i, specification) in self.specifications.iter().enumerate() {
                    match specification.outgoing_traversals(&sources[i], action) {
                        Ok(outgoings) => traversals.push(outgoings.into_iter()),
                        Err(_) => return Err(()),
                    }
                }

                return Ok(Traversal::combinations(traversals.into_iter()).collect());
            }

            let mut found_unique = false;
            for (i, specification) in self.specifications.iter().enumerate() {
                let mut traversals = Vec::with_capacity(self.specifications.len());

                if !found_unique && self.unique_actions[i].contains(&action) {
                    found_unique = true;
                    match specification.outgoing_traversals(&sources[i], action) {
                        Ok(outgoings) => traversals.push(outgoings.into_iter()),
                        Err(_) => return Err(()),
                    }
                } else {
                    let stay = Traversal::stay(sources[i].clone());
                    traversals.push(vec![stay].into_iter());
                }
            }
        }

        return Err(());
    }

    fn location(&self, tree: &LocationTree) -> Result<Location, ()> {
        if let LocationTree::Branch(locations) = tree {
            if locations.len() != self.size() {
                return Err(());
            }

            let sub_locations = locations
                .iter()
                .enumerate()
                .map(|(i, location)| self.specifications[i].location(location));

            if sub_locations
                .clone()
                .any(|sub_location| sub_location.is_err())
            {
                return Err(());
            }

            return Ok(Location::combine(
                sub_locations.map(|sub_location| sub_location.unwrap()),
            ));
        }

        Err(())
    }
}
