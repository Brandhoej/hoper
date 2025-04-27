use std::collections::HashSet;

use crate::zones::constraint::Clock;

use super::{
    action::Action,
    channel::{self, Channel},
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

    pub fn common_actions(&self) -> impl Iterator<Item = &Action> {
        self.common_actions.iter()
    }

    pub fn lhs_unique_actions(&self) -> impl Iterator<Item = &Action> {
        self.lhs_unique_actions.iter()
    }

    pub fn rhs_unique_actions(&self) -> impl Iterator<Item = &Action> {
        self.rhs_unique_actions.iter()
    }

    fn lhs_outgoing_traversals(
        &self,
        source: &LocationTree,
        channel: Channel,
    ) -> Result<Vec<Traversal>, ()> {
        self.lhs
            .channel(*channel.action())
            .ok_or(())
            .and_then(|channel| self.lhs.outgoing_traversals(source, channel))
    }

    fn rhs_outgoing_traversals(
        &self,
        source: &LocationTree,
        channel: Channel,
    ) -> Result<Vec<Traversal>, ()> {
        self.rhs
            .channel(*channel.action())
            .ok_or(())
            .and_then(|channel| self.rhs.outgoing_traversals(source, channel))
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
        channel: Channel,
    ) -> Result<Vec<Traversal>, ()> {
        if !self.channels().contains(&channel) {
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

            if self.common_actions.contains(channel.action()) {
                lhs_traversals = self.lhs.outgoing_traversals(
                    lhs_location,
                    self.lhs.channel(*channel.action()).unwrap(),
                );
                rhs_traversals = self.rhs.outgoing_traversals(
                    rhs_location,
                    self.rhs.channel(*channel.action()).unwrap(),
                );
            } else if self.lhs_unique_actions.contains(channel.action()) {
                lhs_traversals = self.lhs.outgoing_traversals(
                    lhs_location,
                    self.lhs.channel(*channel.action()).unwrap(),
                );
                let stay = Traversal::stay(rhs_location.clone());
                rhs_traversals = Ok(vec![stay]);
            } else if self.rhs_unique_actions.contains(channel.action()) {
                let stay = Traversal::stay(lhs_location.clone());
                lhs_traversals = Ok(vec![stay]);
                rhs_traversals = self.rhs.outgoing_traversals(
                    rhs_location,
                    self.rhs.channel(*channel.action()).unwrap(),
                );
            }

            if lhs_traversals.is_err() || rhs_traversals.is_err() {
                return Err(());
            }

            let combinations: Vec<Traversal> = Traversal::combinations(
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
        match tree {
            LocationTree::Branch(locations) if locations.len() == 2 => {
                let lhs_location = self.lhs.location(&locations[0])?;
                let rhs_location = self.rhs.location(&locations[1])?;

                return Ok(Location::combine(
                    vec![lhs_location, rhs_location].into_iter(),
                ));
            }

            _ => Err(()),
        }
    }

    fn edge(&self, tree: &EdgeTree) -> Result<Edge, ()> {
        match tree {
            EdgeTree::Branch(edges) if edges.len() == 2 => {
                if edges.len() != 2 {
                    return Err(());
                }

                let mut edge_composition: Vec<Edge> = Vec::with_capacity(2);
                let mut action: Option<Action> = None;

                if !edges[0].is_identity() {
                    let lhs_edge = self.lhs.edge(&edges[0])?;
                    edge_composition.push(lhs_edge.clone());
                    action = Some(lhs_edge.action().clone());
                }

                if !edges[1].is_identity() {
                    let rhs_edge = self.rhs.edge(&edges[1])?;
                    edge_composition.push(rhs_edge.clone());
                    action = Some(rhs_edge.action().clone());
                }

                return if let Some(channel) = self.channel(action.unwrap()) {
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

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use crate::automata::{
        automaton::{Automaton, IntoAutomaton},
        automaton_builder::AutomatonBuilder,
        input_enabled::InputEnabled,
        partitioned_symbol_table::PartitionedSymbolTable,
    };

    use super::Composition;

    fn new_automaton_a(symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        let loc0_symbol = builder.add_symbol(1, "a0");
        let loc0 = builder.add_location(loc0_symbol, None);
        builder.set_initial_location(loc0);
        builder.build().unwrap()
    }

    fn new_automaton_b(symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        // Global declarations:
        let bc_action = builder.add_symbol(0, "bc");

        // Local declarations:
        let loc0_symbol = builder.add_symbol(2, "b0");
        let loc1_symbol = builder.add_symbol(2, "b1");

        // Build:
        let loc0 = builder.add_location(loc0_symbol, None);
        let loc1 = builder.add_location(loc1_symbol, None);
        builder.set_initial_location(loc0);

        builder.add_edge_input(loc0, loc1, bc_action, None, None);

        builder.build().unwrap()
    }

    fn new_automaton_c(symbols: &mut PartitionedSymbolTable) -> Automaton {
        let mut builder = AutomatonBuilder::new(symbols);
        // Global declarations:
        let bc_action = builder.add_symbol(0, "bc");

        // Local declarations:
        let c_action = builder.add_symbol(3, "c");
        let loc0_symbol = builder.add_symbol(3, "c0");
        let loc1_symbol = builder.add_symbol(3, "c1");
        let loc2_symbol = builder.add_symbol(3, "c2");

        // Build:
        let loc0 = builder.add_location(loc0_symbol, None);
        let loc1 = builder.add_location(loc1_symbol, None);
        let loc2 = builder.add_location(loc2_symbol, None);
        builder.set_initial_location(loc0);

        builder.add_edge_input(loc0, loc1, c_action, None, None);
        builder.add_edge_input(loc1, loc2, bc_action, None, None);

        builder.build().unwrap()
    }

    #[test]
    fn automaton_a() {
        let mut symbols = PartitionedSymbolTable::new();
        let automaton = new_automaton_a(&mut symbols);

        /*let contextual_automaton = automaton.in_context(&symbols);
        println!("{}", contextual_automaton.dot());*/

        assert_eq!(automaton.inputs().try_len().unwrap(), 0);
        assert_eq!(automaton.outputs().try_len().unwrap(), 0);
        assert_eq!(automaton.node_iter().try_len().unwrap(), 1);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 0);
    }

    #[test]
    fn automaton_b() {
        let mut symbols = PartitionedSymbolTable::new();
        let automaton = new_automaton_b(&mut symbols);

        /*let contextual_automaton = automaton.in_context(&symbols);
        println!("{}", contextual_automaton.dot());*/

        assert_eq!(automaton.inputs().try_len().unwrap(), 1);
        assert_eq!(automaton.outputs().try_len().unwrap(), 0);
        assert_eq!(automaton.node_iter().try_len().unwrap(), 2);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 1);
    }

    #[test]
    fn automaton_c() {
        let mut symbols = PartitionedSymbolTable::new();
        let automaton = new_automaton_c(&mut symbols);

        /*let contextual_automaton = automaton.in_context(&symbols);
        println!("{}", contextual_automaton.dot());*/

        assert_eq!(automaton.inputs().try_len().unwrap(), 2);
        assert_eq!(automaton.outputs().try_len().unwrap(), 0);
        assert_eq!(automaton.node_iter().try_len().unwrap(), 3);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 2);
    }

    #[test]
    fn automaton_a_self_composition() {
        let mut symbols = PartitionedSymbolTable::new();
        let lhs = new_automaton_a(&mut symbols);
        let rhs = new_automaton_a(&mut symbols);
        let composition = Composition::new(
            lhs.is_input_enabled().unwrap(),
            rhs.is_input_enabled().unwrap(),
        )
        .unwrap();
        let automaton = composition.into_automaton().unwrap();

        /*let contextual_automaton = automaton.in_context(&symbols);
        println!("{}", contextual_automaton.dot());*/

        assert_eq!(automaton.inputs().try_len().unwrap(), 0);
        assert_eq!(automaton.outputs().try_len().unwrap(), 0);
        assert_eq!(automaton.node_iter().try_len().unwrap(), 1);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 0);
    }

    #[test]
    fn automaton_b_self_composition() {
        let mut symbols = PartitionedSymbolTable::new();
        let lhs = new_automaton_b(&mut symbols);
        let rhs = new_automaton_b(&mut symbols);
        let composition = Composition::new(
            lhs.is_input_enabled().unwrap(),
            rhs.is_input_enabled().unwrap(),
        )
        .unwrap();
        let automaton = composition.into_automaton().unwrap();

        /*let contextual_automaton = automaton.in_context(&symbols);
        println!("{}", contextual_automaton.dot());*/

        assert_eq!(automaton.inputs().try_len().unwrap(), 1);
        assert_eq!(automaton.outputs().try_len().unwrap(), 0);
        assert_eq!(automaton.node_iter().try_len().unwrap(), 2);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 1);
    }

    #[test]
    fn automaton_c_self_composition() {
        let mut symbols = PartitionedSymbolTable::new();
        let lhs = new_automaton_c(&mut symbols);
        let rhs = new_automaton_c(&mut symbols);
        let composition = Composition::new(
            lhs.is_input_enabled().unwrap(),
            rhs.is_input_enabled().unwrap(),
        )
        .unwrap();
        let automaton = composition.into_automaton().unwrap();

        /*let contextual_automaton = automaton.in_context(&symbols);
        println!("{}", contextual_automaton.dot());*/

        assert_eq!(automaton.inputs().try_len().unwrap(), 2);
        assert_eq!(automaton.outputs().try_len().unwrap(), 0);
        assert_eq!(automaton.node_iter().try_len().unwrap(), 3);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 2);
    }

    #[test]
    fn automaton_b_c_composition() {
        let mut symbols = PartitionedSymbolTable::new();
        let lhs = new_automaton_b(&mut symbols);
        let rhs = new_automaton_c(&mut symbols);
        let composition = Composition::new(
            lhs.is_input_enabled().unwrap(),
            rhs.is_input_enabled().unwrap(),
        )
        .unwrap();
        let automaton = composition.into_automaton().unwrap();

        /*let contextual_automaton = automaton.in_context(&symbols);
        println!("{}", contextual_automaton.dot());*/

        assert_eq!(automaton.inputs().try_len().unwrap(), 2);
        assert_eq!(automaton.outputs().try_len().unwrap(), 0);
        assert_eq!(automaton.node_iter().try_len().unwrap(), 3);
        assert_eq!(automaton.edge_iter().try_len().unwrap(), 2);
    }
}
