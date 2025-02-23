use std::collections::{HashSet, VecDeque};

use itertools::Itertools;

use crate::{automata::tiots::TIOTS, zones::intervals::Interval};

use super::{
    action::Action, ioa::IOA, specification::Specification, state_set::StateSet, tioa::Traversal,
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

    pub fn initial(&self) -> Result<RefinementStatePair, ()> {
        let implementation_state = self.implementation.initial_state();
        if let Err(()) = implementation_state {
            return Err(());
        }

        let specification_state = self.specification.initial_state();
        if let Err(()) = specification_state {
            return Err(());
        }

        RefinementStatePair::from_states(
            implementation_state.unwrap(),
            specification_state.unwrap(),
        )
    }

    pub fn refines(&self) -> bool {
        // TODO: Use crossbeam to multi-thread the refinment check.
        // An example where work is shared between threads can be seen here:
        // https://docs.rs/crossbeam/latest/crossbeam/deque/index.html

        let mut implementation_passed: StateSet = StateSet::new();
        let mut specification_passed: StateSet = StateSet::new();
        let mut worklist: VecDeque<RefinementStatePair> = VecDeque::new();

        // (qᔆ₀, qᵀ₀) ∈ R
        match self.initial() {
            Ok(initial) => {
                implementation_passed.insert(initial.implementation());
                specification_passed.insert(initial.specification());
                worklist.push_back(initial)
            }
            Err(_) => return false,
        };

        while let Some(pair) = worklist.pop_front() {
            let len = worklist.len();
            println!("{}", len);

            let mut products: Vec<
                Box<dyn Iterator<Item = ((State, Traversal), (State, Traversal))>>,
            > = Vec::with_capacity(4);

            // Rule 1 (Common inputs): Both the specification and implementaion can react on the input.
            // Whenever t -i?->ᵀ t' for some t' ∈ Qᵀ and i? ∈ Actᵀᵢ ∩ Actᔆᵢ , then s -i?->ᔆ s' and (s', t') ∈ R for some s' ∈ Qᔆ
            for input in self.common_inputs.iter() {
                let mut specification_states = self
                    .specification
                    .traversals(&pair.specification(), input)
                    .peekable();

                let mut implementation_states = self
                    .implementation
                    .traversals(&pair.implementation(), input)
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
            for input in self.unique_specification_inputs.iter() {
                let mut specification_states = self
                    .specification
                    .traversals(pair.specification(), input)
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
            for output in self.common_outputs.iter() {
                let mut implementation_states = self
                    .implementation
                    .traversals(pair.implementation(), output)
                    .peekable();

                // Only if the implementation can produce an output is it
                // required that the specification also can produce the output.
                if implementation_states.peek().is_none() {
                    continue;
                }

                // The specification should be able to produce the output since the implementation can.
                let mut specification_states = self
                    .specification
                    .traversals(pair.specification(), output)
                    .peekable();

                // The specification could not produce the output the implementation could.
                if specification_states.peek().is_none() {
                    return false;
                }

                products.push(Box::new(
                    implementation_states.cartesian_product(specification_states),
                ))
            }

            // Rule 4 (Unique implementation outputs): Only the implementation can produce the output.
            // Whenever s -o!->ᔆ s' for some s' ∈ Qᔆ and o! ∈ Actᵀₒ \ Actᔆₒ, then (s', t) ∈ R.
            for output in self.unique_implementation_outputs.iter() {
                let mut implementation_states = self
                    .implementation
                    .traversals(pair.implementation(), output)
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

            let original_implementation_interval = pair.implementation.ref_zone().interval();
            let original_specification_interval = pair.specification.ref_zone().interval();

            for product in products {
                for (
                    (mut implementation_state, implementation_traversal),
                    (mut specification_state, specification_traversal),
                ) in product
                {
                    let implementation_interval = implementation_state.ref_zone().interval();
                    let implementation_start = original_implementation_interval
                        .lower()
                        .difference(implementation_interval.lower());
                    let implementation_end =
                        implementation_start + implementation_interval.included();
                    let adjusted_implementation_interval =
                        Interval::new(implementation_start, implementation_end);

                    let specification_interval = specification_state.ref_zone().interval();
                    let specification_start = original_specification_interval
                        .lower()
                        .difference(specification_interval.lower());
                    let specification_end = specification_start + specification_interval.included();
                    let adjusted_specification_interval =
                        Interval::new(specification_start, specification_end);

                    // The adjusted intervals do not overlap. This means that the two edges were not enabled at the same time.
                    if adjusted_specification_interval
                        .intersection(&adjusted_implementation_interval)
                        .is_none()
                    {
                        continue;
                    }

                    // Perform the traversal of the edges (Implementation and specification):
                    implementation_state = self
                        .implementation
                        .discrete(implementation_state, &implementation_traversal)
                        .unwrap();
                    implementation_state = self.implementation.delay(implementation_state).unwrap();

                    specification_state = self
                        .specification
                        .discrete(specification_state, &specification_traversal)
                        .unwrap();
                    specification_state = self.specification.delay(specification_state).unwrap();

                    match RefinementStatePair::from_states(
                        implementation_state,
                        specification_state,
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
                                worklist.push_back(pair);
                            }
                        }
                        Err(_) => return false,
                    };
                }
            }
        }

        true
    }
}
