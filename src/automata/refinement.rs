use std::collections::{HashSet, VecDeque};

use crate::{automata::tiots::TIOTS, zones::federation::Federation};

use super::{
    action::Action, ioa::IOA, specification::Specification, state_set::StateSet,
    tioa::LocationTree, tiots::State,
};

#[derive(Clone)]
pub struct RefinementStatePair {
    implementation: LocationTree,
    specification: LocationTree,
    federation: Federation,
}

impl RefinementStatePair {
    pub fn new(
        implementation: LocationTree,
        specification: LocationTree,
        federation: Federation,
    ) -> Self {
        Self {
            implementation,
            specification,
            federation,
        }
    }

    pub fn from_states(implementation: State, specification: State) -> Result<Self, ()> {
        // Rule 5 (Time consistency): When the implementation requires a delay so must the specification.
        // Whenever s -d->ᔆ s' for some s' ∈ Qᔆ and d ∈ ℝ≥0, then t -d->ᵀ t' and (s', t') ∈ R for some t' ∈ Qᵀ.

        let (implementation_location, implementation_federation) = implementation.decompose();
        let (specification_location, specification_federation) = specification.decompose();

        if implementation_federation.is_empty() {
            return Ok(Self::new(
                implementation_location,
                specification_location,
                implementation_federation,
            ));
        }

        if specification_federation.is_empty() {
            return Err(());
        }

        if !implementation_federation.is_subset(&specification_federation) {
            return Err(());
        }

        Ok(Self::new(
            implementation_location,
            specification_location,
            // Only the clock valuations where the implementation can transition should the specification also transition.
            implementation_federation.intersection(specification_federation),
        ))
    }

    pub fn implementation(&self) -> LocationTree {
        self.implementation.clone()
    }

    pub fn specification(&self) -> LocationTree {
        self.specification.clone()
    }

    pub fn federation(&self) -> &Federation {
        &self.federation
    }

    pub fn implementation_state(&self) -> State {
        State::new(self.implementation.clone(), self.federation.clone())
    }

    pub fn specification_state(&self) -> State {
        State::new(self.specification.clone(), self.federation.clone())
    }
}

impl From<RefinementStatePair> for State {
    fn from(value: RefinementStatePair) -> Self {
        Self::new(
            LocationTree::new_branch(vec![value.implementation, value.specification]),
            value.federation,
        )
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
        if !specification.inputs().is_subset(&implementation.inputs()) {
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
        RefinementStatePair::from_states(
            self.implementation.initial_state(),
            self.specification.initial_state(),
        )
    }

    pub fn refines(&self) -> bool {
        let mut passed: StateSet = StateSet::new();
        let mut worklist: VecDeque<RefinementStatePair> = VecDeque::new();

        // (qᔆ₀, qᵀ₀) ∈ R
        match self.initial() {
            Ok(initial) => worklist.push_back(initial),
            Err(_) => return false,
        };

        while !worklist.is_empty() {
            let pair = worklist.pop_front().unwrap();

            let mut states: Vec<(
                Box<dyn Iterator<Item = State>>,
                Box<dyn Iterator<Item = State>>,
            )> = Vec::new();

            // Rule 1 (Common inputs): Both the specification and implementaion can react on the input.
            // Whenever t -i?->ᵀ t' for some t' ∈ Qᵀ and i? ∈ Actᵀᵢ ∩ Actᔆᵢ , then s -i?->ᔆ s' and (s', t') ∈ R for some s' ∈ Qᔆ
            for input in self.common_inputs.iter() {
                let mut specification_states = self
                    .specification
                    .states_from(pair.specification_state(), *input)
                    .unwrap()
                    .peekable();

                // Only when the specification can react to the common input should
                // the implementation also be able to react to the input.
                if specification_states.peek().is_none() {
                    continue;
                }

                let mut implementation_states = self
                    .implementation
                    .states_from(pair.implementation_state(), *input)
                    .unwrap()
                    .peekable();

                // The implementation could not react to the input.
                if implementation_states.peek().is_none() {
                    return false;
                }

                states.push((
                    Box::new(implementation_states),
                    Box::new(specification_states),
                ));
            }

            // Rule 2 (Unique specification inputs): Only the specification reacts to the input.
            // Whenever t -i?->ᵀ t' for some t' ∈ Qᵀ and i? ∈ Actᵀᵢ \ Actᔆᵢ, then (s, t') ∈ R.
            for input in self.unique_specification_inputs.iter() {
                let mut specification_states = self
                    .specification
                    .states_from(pair.specification_state(), *input)
                    .unwrap()
                    .peekable();

                if specification_states.peek().is_none() {
                    continue;
                }

                states.push((
                    Box::new(Box::new(std::iter::once(pair.implementation_state()))),
                    Box::new(specification_states),
                ));
            }

            // Rule 3 (Common outputs): Both the specification and implementaion can produce the output.
            // Whenever s -o!->ᔆ s' for some s' ∈ Qᔆ and o! ∈ Actᵀₒ ∩ Actᔆₒ , then t -o!->ᵀ t' and (s', t') ∈ R for some t' ∈ Qᵀ
            for output in self.common_outputs.iter() {
                let mut implementation_states = self
                    .implementation
                    .states_from(pair.implementation_state(), *output)
                    .unwrap()
                    .peekable();

                // Only if the implementation can produce an output is it
                // required that the specification also can produce the output.
                if implementation_states.peek().is_none() {
                    continue;
                }

                // The specification should be able to produce the output since the implementation can.
                let mut specification_states = self
                    .specification
                    .states_from(pair.specification_state(), *output)
                    .unwrap()
                    .peekable();

                // The specification could not prduce the outptu the implementation could.
                if specification_states.peek().is_none() {
                    return false;
                }

                states.push((
                    Box::new(implementation_states),
                    Box::new(specification_states),
                ));
            }

            // Rule 4 (Unique implementation outputs): Only the implementation can produce the output.
            // Whenever s -o!->ᔆ s' for some s' ∈ Qᔆ and o! ∈ Actᵀₒ \ Actᔆₒ, then (s', t) ∈ R.
            for output in self.unique_implementation_outputs.iter() {
                let mut implementation_states = self
                    .implementation
                    .states_from(pair.implementation_state(), *output)
                    .unwrap()
                    .peekable();

                if implementation_states.peek().is_none() {
                    continue;
                }

                states.push((
                    Box::new(implementation_states),
                    Box::new(Box::new(std::iter::once(pair.specification_state()))),
                ));
            }

            for (implementation_states_iter, specification_states_iter) in states {
                let specification_states: Vec<State> = specification_states_iter.collect();

                for implementation_state in implementation_states_iter {
                    for specification_state in specification_states.iter() {
                        match RefinementStatePair::from_states(
                            implementation_state.clone(),
                            specification_state.clone(),
                        ) {
                            Ok(state) => {
                                if !passed.contains(state.clone().into()) {
                                    passed.insert(state.clone().into());
                                    worklist.push_back(state);
                                }
                            }
                            Err(_) => return false,
                        }
                    }
                }
            }
        }

        true
    }
}
