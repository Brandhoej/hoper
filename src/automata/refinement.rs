use std::collections::{HashSet, VecDeque};

use itertools::Itertools;
use petgraph::graph::NodeIndex;

use crate::automata::tiots::TIOTS;

use super::{
    action::Action,
    computation_tree::ComputationTree,
    ioa::IOA,
    specification::Specification,
    state_set::StateSet,
    tioa::{LocationTree, Traversal, TIOA},
    tiots::State,
};

#[derive(Clone)]
pub struct RefinementStatePair {
    implementation: State,
    specification: State,
}

impl RefinementStatePair {
    pub fn new(implementation: State, specification: State) -> Self {
        Self {
            implementation,
            specification,
        }
    }

    pub fn from_states(implementation: State, mut specification: State) -> Result<Self, ()> {
        // Rule 5 (Time consistency): When the implementation requires a delay so must the specification.
        // Whenever s -d->ᔆ s' for some s' ∈ Qᔆ and d ∈ ℝ≥0, then t -d->ᵀ t' and (s', t') ∈ R for some t' ∈ Qᵀ.
        // In other words: The implementation can be faster than the specification, but not slower.

        let implementation_interval = implementation.ref_zone().interval();
        let specification_interval = specification.ref_zone().interval();

        // The implementation uses more time than the specification and is thereby slower.
        if implementation_interval.included() > specification_interval.included() {
            return Err(());
        }

        // The specification is more loose and has delayed more than the implementation.
        // The delays should be synchronised and therefore, the specificaiton has to be un-delayed.
        if specification_interval.included() > implementation_interval.included() {
            specification
                .mut_zone()
                .delay_to(implementation_interval.included());
        }

        Ok(RefinementStatePair::new(implementation, specification))
    }

    pub fn implementation(&self) -> &State {
        &self.implementation
    }

    pub fn specification(&self) -> &State {
        &self.specification
    }
}

/// S ≤ T where S is the implementation and T is the specification.
/// Both are required to be specifications however by conventions the names can be confusing.
pub struct Refinement {
    implementation: Box<Specification>,
    specification: Box<Specification>,
    common_inputs: HashSet<Action>,
    common_outputs: HashSet<Action>,
    unique_specification_inputs: HashSet<Action>,
    unique_implementation_outputs: HashSet<Action>,
}

impl Refinement {
    pub fn new(
        implementation: Box<Specification>,
        specification: Box<Specification>,
    ) -> Result<Self, ()> {
        // Actᔆᵢ ∩ Actᵀₒ = ∅
        if !implementation
            .inputs()
            .is_disjoint(&specification.outputs())
        {
            return Err(());
        }

        // Actᔆₒ ∩ Actᵀᵢ = ∅
        if !implementation
            .outputs()
            .is_disjoint(&specification.inputs())
        {
            return Err(());
        }

        // Actᔆᵢ ⊆ Actᵀᵢ
        if !implementation.inputs().is_subset(&specification.inputs()) {
            return Err(());
        }

        // Actᵀₒ ⊆ Actᔆₒ
        if !specification.outputs().is_subset(&implementation.outputs()) {
            return Err(());
        }

        // i? ∈ Actᵀᵢ ∩ Actᔆᵢ
        let common_inputs = specification
            .inputs()
            .intersection(&implementation.inputs())
            .cloned()
            .collect();

        // i? ∈ Actᵀᵢ \ Actᔆᵢ
        let unique_specification_inputs = specification
            .inputs()
            .difference(&implementation.inputs())
            .cloned()
            .collect();

        // o! ∈ Actᔆₒ ∩ Actᵀₒ
        let common_outputs = specification
            .outputs()
            .intersection(&implementation.outputs())
            .cloned()
            .collect();

        // o! ∈ Actᔆₒ \ Actᵀₒ
        let unique_implementation_outputs = implementation
            .outputs()
            .difference(&specification.outputs())
            .cloned()
            .collect();

        Ok(Self {
            implementation,
            specification,
            common_inputs,
            common_outputs,
            unique_specification_inputs,
            unique_implementation_outputs,
        })
    }

    pub fn initial_locations(&self) -> (LocationTree, LocationTree) {
        (
            self.implementation.initial_location(),
            self.specification.initial_location(),
        )
    }

    pub fn initial(&self) -> Result<RefinementStatePair, ()> {
        let implementation_state = self.implementation.initial_state();
        if let Err(()) = implementation_state {
            return Err(());
        }

        let specification_state = self.specification.initial_state();
        if let Err(()) = specification_state {
            return Err(());
        }

        // FIXME: THESE ARE NOT SYNCHRONISED AND ALLOW DIFFERENT INITIAL DELAYS.
        println!(
            "{}",
            implementation_state
                .clone()
                .unwrap()
                .ref_zone()
                .fmt_conjunctions(&vec!["x", "y"])
        );
        println!(
            "{}",
            specification_state
                .clone()
                .unwrap()
                .ref_zone()
                .fmt_conjunctions(&vec!["x", "y"])
        );

        RefinementStatePair::from_states(
            implementation_state.unwrap(),
            specification_state.unwrap(),
        )
    }

    pub fn refines(
        &self,
    ) -> Result<(ComputationTree, ComputationTree), (ComputationTree, ComputationTree)> {
        // TODO: Use crossbeam to multi-thread the refinment check.
        // An example where work is shared between threads can be seen here:
        // https://docs.rs/crossbeam/latest/crossbeam/deque/index.html

        let mut implementation_passed: StateSet = StateSet::new();
        let mut specification_passed: StateSet = StateSet::new();
        let mut worklist: VecDeque<(NodeIndex, NodeIndex, RefinementStatePair)> = VecDeque::new();

        let (root_implementation_tree, root_specification_tree) = self.initial_locations();
        let mut implementation_computation_tree = ComputationTree::new(root_implementation_tree);
        let mut specification_computation_tree = ComputationTree::new(root_specification_tree);

        // (qᔆ₀, qᵀ₀) ∈ R
        match self.initial() {
            Ok(initial) => {
                implementation_passed.insert(initial.implementation());
                specification_passed.insert(initial.specification());

                worklist.push_back((
                    implementation_computation_tree.root(),
                    specification_computation_tree.root(),
                    initial,
                ))
            }
            Err(_) => {
                implementation_computation_tree.is_error(implementation_computation_tree.root());
                specification_computation_tree.is_error(specification_computation_tree.root());

                return Err((
                    implementation_computation_tree,
                    specification_computation_tree,
                ));
            }
        };

        while let Some((source_implementation, source_specification, pair)) = worklist.pop_front() {
            let mut products: Vec<
                Box<dyn Iterator<Item = ((State, Traversal), (State, Traversal))>>,
            > = Vec::with_capacity(4);

            // Rule 1 (Common inputs): Both the specification and implementaion can react on the input.
            // Whenever t -i?->ᵀ t' for some t' ∈ Qᵀ and i? ∈ Actᵀᵢ ∩ Actᔆᵢ , then s -i?->ᔆ s' and (s', t') ∈ R for some s' ∈ Qᔆ
            for action in self.common_inputs.iter() {
                let channel = action.input();
                let mut specification_states = self
                    .specification
                    .enabled(&pair.specification(), channel.clone())
                    .peekable();

                let mut implementation_states = self
                    .implementation
                    .enabled(&pair.implementation(), channel.clone())
                    .peekable();

                // I believe that since both are specifications then thet must both be input-enabled.
                // Because of this of this, they would all in all states be able to react to all inputs.
                assert!(specification_states.peek().is_some());
                assert!(implementation_states.peek().is_some());

                products.push(Box::new(
                    implementation_states.cartesian_product(specification_states),
                ));
            }

            // Rule 2 (Unique specification inputs): Only the specification reacts to the input.
            // Whenever t -i?->ᵀ t' for some t' ∈ Qᵀ and i? ∈ Actᵀᵢ \ Actᔆᵢ, then (s, t') ∈ R.
            for action in self.unique_specification_inputs.iter() {
                let channel = action.input();
                let mut specification_states = self
                    .specification
                    .enabled(pair.specification(), channel)
                    .peekable();

                // I believe that since both are specifications then thet must both be input-enabled.
                // Because of this of this, they would all in all states be able to react to all inputs.
                assert!(specification_states.peek().is_some());

                let implementation_states = vec![(
                    pair.implementation().clone(),
                    Traversal::stay(pair.implementation().location().clone()),
                )];

                products.push(Box::new(
                    implementation_states
                        .into_iter()
                        .cartesian_product(specification_states),
                ))
            }

            // Rule 3 (Common outputs): Both the specification and implementaion can produce the output.
            // Whenever s -o!->ᔆ s' for some s' ∈ Qᔆ and o! ∈ Actᵀₒ ∩ Actᔆₒ then t -o!->ᵀ t' and (s', t') ∈ R for some t' ∈ Qᵀ
            for action in self.common_outputs.iter() {
                let channel = action.output();
                let mut implementation_states = self
                    .implementation
                    .enabled(pair.implementation(), channel.clone())
                    .peekable();

                // Only if the implementation can produce an output is it
                // required that the specification also can produce the output.
                if implementation_states.peek().is_none() {
                    continue;
                }

                // The specification should be able to produce the output since the implementation can.
                let mut specification_states = self
                    .specification
                    .enabled(pair.specification(), channel.clone())
                    .peekable();

                // The specification could not produce the output the implementation could.
                if specification_states.peek().is_none() {
                    implementation_computation_tree.is_error(source_implementation);
                    specification_computation_tree.is_error(source_specification);

                    return Err((
                        implementation_computation_tree,
                        specification_computation_tree,
                    ));
                }

                products.push(Box::new(
                    implementation_states.cartesian_product(specification_states),
                ))
            }

            // Rule 4 (Unique implementation outputs): Only the implementation can produce the output.
            // Whenever s -o!->ᔆ s' for some s' ∈ Qᔆ and o! ∈ Actᵀₒ \ Actᔆₒ, then (s', t) ∈ R.
            for action in self.unique_implementation_outputs.iter() {
                let channel = action.output();
                let mut implementation_states = self
                    .implementation
                    .enabled(pair.implementation(), channel.clone())
                    .peekable();

                if implementation_states.peek().is_none() {
                    continue;
                }

                let specification_states = vec![(
                    pair.specification().clone(),
                    Traversal::stay(pair.specification().location().clone()),
                )];

                products.push(Box::new(
                    implementation_states
                        .into_iter()
                        .cartesian_product(specification_states),
                ))
            }

            for product in products {
                for (
                    (mut implementation_state, implementation_traversal),
                    (mut specification_state, specification_traversal),
                ) in product
                {
                    println!("");
                    println!(
                        "Implementation location: {} -{}-> {}",
                        pair.implementation.location(),
                        implementation_traversal.edge(),
                        implementation_traversal.destination()
                    );
                    println!(
                        "Specification location: {} -{}-> {}",
                        pair.specification.location(),
                        specification_traversal.edge(),
                        specification_traversal.destination()
                    );
                    println!(
                        "Before implementation: {}",
                        pair.implementation
                            .ref_zone()
                            .fmt_conjunctions(&vec!["x", "y"])
                    );
                    println!(
                        "Before specification: {}",
                        pair.specification
                            .ref_zone()
                            .fmt_conjunctions(&vec!["x", "y"])
                    );

                    // Ensure that they are they are enabled at the same time.
                    let implementation_delay_by = pair
                        .implementation
                        .ref_zone()
                        .delayed_by(implementation_state.ref_zone());
                    let specification_delay_by = pair
                        .specification
                        .ref_zone()
                        .delayed_by(specification_state.ref_zone());

                    match implementation_delay_by.intersection(&specification_delay_by) {
                        Some(intersection) => {
                            println!("Enabled intersection: {}", intersection);
                            implementation_state.mut_zone().clamp_inside(intersection);
                            specification_state.mut_zone().clamp_inside(intersection);
                        }
                        None => continue,
                    }

                    println!(
                        "Enabled implementation: {}",
                        implementation_state
                            .ref_zone()
                            .fmt_conjunctions(&vec!["x", "y"])
                    );
                    println!(
                        "Enabled specification: {}",
                        specification_state
                            .ref_zone()
                            .fmt_conjunctions(&vec!["x", "y"])
                    );

                    // Traverse
                    implementation_state = self
                        .implementation
                        .traverse(implementation_state, &implementation_traversal)
                        .unwrap();
                    specification_state = self
                        .specification
                        .traverse(specification_state, &specification_traversal)
                        .unwrap();

                    println!(
                        "Traversed implementation: {}",
                        implementation_state
                            .ref_zone()
                            .fmt_conjunctions(&vec!["x", "y"])
                    );
                    println!(
                        "Traversed specification: {}",
                        specification_state
                            .ref_zone()
                            .fmt_conjunctions(&vec!["x", "y"])
                    );

                    // Delay
                    let mut final_implementation_state = self
                        .implementation
                        .delay(implementation_state.clone())
                        .unwrap();
                    let mut final_specification_state = self
                        .specification
                        .delay(specification_state.clone())
                        .unwrap();

                    println!(
                        "Delayed implementation: {}",
                        final_implementation_state
                            .ref_zone()
                            .fmt_conjunctions(&vec!["x", "y"])
                    );
                    println!(
                        "Delayed specification: {}",
                        final_specification_state
                            .ref_zone()
                            .fmt_conjunctions(&vec!["x", "y"])
                    );

                    // Ensure that they delay the same.
                    let implementation_delay_by = implementation_state
                        .ref_zone()
                        .delayed_by(final_implementation_state.ref_zone());
                    let specification_delay_by = specification_state
                        .ref_zone()
                        .delayed_by(final_specification_state.ref_zone());

                    match implementation_delay_by.intersection(&specification_delay_by) {
                        Some(intersection) => {
                            println!("Delay intersection: {}", intersection);
                            final_implementation_state
                                .mut_zone()
                                .clamp_inside(intersection);
                            final_specification_state
                                .mut_zone()
                                .clamp_inside(intersection);
                        }
                        None => continue,
                    }

                    println!(
                        "Adjusted by delay implementation: {}",
                        final_implementation_state
                            .ref_zone()
                            .fmt_conjunctions(&vec!["x", "y"])
                    );
                    println!(
                        "Adjusted by delay specification: {}",
                        final_specification_state
                            .ref_zone()
                            .fmt_conjunctions(&vec!["x", "y"])
                    );

                    match RefinementStatePair::from_states(
                        final_implementation_state,
                        final_specification_state,
                    ) {
                        Ok(pair) => {
                            let mut visited = true;

                            if !implementation_passed.contains(pair.implementation()) {
                                implementation_passed.insert(pair.implementation());
                                visited = false
                            }

                            if !specification_passed.contains(pair.specification()) {
                                specification_passed.insert(pair.specification());
                                visited = false
                            }

                            if !visited {
                                let destination_implementation = implementation_computation_tree
                                    .enqueue(source_implementation, implementation_traversal);
                                let destination_specification = specification_computation_tree
                                    .enqueue(source_specification, specification_traversal);

                                worklist.push_back((
                                    destination_implementation,
                                    destination_specification,
                                    pair,
                                ));
                            }
                        }
                        Err(_) => {
                            let destination_implementation = implementation_computation_tree
                                .enqueue(source_implementation, implementation_traversal);
                            let destination_specification = specification_computation_tree
                                .enqueue(source_specification, specification_traversal);

                            implementation_computation_tree.is_error(destination_implementation);
                            specification_computation_tree.is_error(destination_specification);

                            return Err((
                                implementation_computation_tree,
                                specification_computation_tree,
                            ));
                        }
                    };
                }
            }

            implementation_computation_tree.dequeue(source_implementation);
            specification_computation_tree.dequeue(source_specification);
        }

        Ok((
            implementation_computation_tree,
            specification_computation_tree,
        ))
    }
}
