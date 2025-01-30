use std::{
    collections::{HashSet, VecDeque},
    iter,
};

use itertools::Itertools;

use crate::automata::tiots::TIOTS;

use super::{
    action::Action, ioa::IOA, specification::Specification, state_set::StateSet, tiots::State,
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

        // The specification cannot match the implementation's delay.
        let specification_delay = specification.ref_zone().delays();
        let implementation_delay = implementation.ref_zone().delays();
        if specification_delay < implementation_delay {
            return Err(());
        }

        // The specification delays more than the implementation. But it should only at the maximum match the delay.
        if specification_delay > implementation_delay {
            specification
                .mut_zone()
                .delay(implementation_delay - specification_delay);
        }

        Ok(Self::new(implementation, specification))
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
        // FIXME: Only consider

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
        // FIXME: Assumes that two edges which are not enabled under the same delays are valid pairs.
        // Eg. The Specification has "0 -u<=2-> 1" and "0 -u>2-> 2" which are considered as a pair
        // but they are not enabled under the same delay and therefore should not be considered as pairs.
        // This check only has to be made when the action is common (both for inputs and outputs).
        // Solution idea: Instead of two boxed iterators of states, then one iterator of a state tuple.

        // TODO: Use crossbeam to multi-thread the refinment check.
        // An example where work is shared between threads can be seen here:
        // https://docs.rs/crossbeam/latest/crossbeam/deque/index.html

        let mut implementation_passed: StateSet = StateSet::new();
        let mut specification_passed: StateSet = StateSet::new();
        let mut worklist: VecDeque<RefinementStatePair> = VecDeque::new();

        // (qᔆ₀, qᵀ₀) ∈ R
        match self.initial() {
            Ok(initial) => worklist.push_back(initial),
            Err(_) => return false,
        };

        while let Some(pair) = worklist.pop_front() {
            let mut states: Vec<Box<dyn Iterator<Item = (State, State)>>> = Vec::new();

            // Rule 1 (Common inputs): Both the specification and implementaion can react on the input.
            // Whenever t -i?->ᵀ t' for some t' ∈ Qᵀ and i? ∈ Actᵀᵢ ∩ Actᔆᵢ , then s -i?->ᔆ s' and (s', t') ∈ R for some s' ∈ Qᔆ
            for input in self.common_inputs.iter() {
                let mut specification_edges = self
                    .specification
                    .enabled_edges(&pair.specification(), input)
                    .peekable();

                // Only when the specification can react to the common input should
                // the implementation also be able to react to the input.
                if specification_edges.peek().is_none() {
                    continue;
                }

                let mut implementation_states = self
                    .implementation
                    .enabled_edges(&pair.implementation(), input)
                    .peekable();

                // The implementation could not react to the input.
                if implementation_states.peek().is_none() {
                    return false;
                }

                todo!()
                /*states.push(Box::new(Itertools::cartesian_product(
                    implementation_states,
                    specification_edges.collect::<Vec<_>>().into_iter(),
                )));*/
            }

            // Rule 2 (Unique specification inputs): Only the specification reacts to the input.
            // Whenever t -i?->ᵀ t' for some t' ∈ Qᵀ and i? ∈ Actᵀᵢ \ Actᔆᵢ, then (s, t') ∈ R.
            for input in self.unique_specification_inputs.iter() {
                let mut specification_states = self
                    .specification
                    .enabled_edges(pair.specification(), input)
                    .peekable();

                if specification_states.peek().is_none() {
                    continue;
                }

                todo!()
                /*states.push(Box::new(Itertools::cartesian_product(
                    iter::once(pair.implementation()),
                    specification_states.collect::<Vec<_>>().into_iter(),
                )));*/
            }

            // Rule 3 (Common outputs): Both the specification and implementaion can produce the output.
            // Whenever s -o!->ᔆ s' for some s' ∈ Qᔆ and o! ∈ Actᵀₒ ∩ Actᔆₒ , then t -o!->ᵀ t' and (s', t') ∈ R for some t' ∈ Qᵀ
            for output in self.common_outputs.iter() {
                let mut implementation_states = self
                    .implementation
                    .enabled_edges(pair.implementation(), output)
                    .peekable();

                // Only if the implementation can produce an output is it
                // required that the specification also can produce the output.
                if implementation_states.peek().is_none() {
                    continue;
                }

                // The specification should be able to produce the output since the implementation can.
                let mut specification_states = self
                    .specification
                    .enabled_edges(pair.specification(), output)
                    .peekable();

                // The specification could not prduce the outptu the implementation could.
                if specification_states.peek().is_none() {
                    return false;
                }

                todo!()
                /*states.push(Box::new(Itertools::cartesian_product(
                    implementation_states,
                    specification_states.collect::<Vec<_>>().into_iter(),
                )));*/
            }

            // Rule 4 (Unique implementation outputs): Only the implementation can produce the output.
            // Whenever s -o!->ᔆ s' for some s' ∈ Qᔆ and o! ∈ Actᵀₒ \ Actᔆₒ, then (s', t) ∈ R.
            for output in self.unique_implementation_outputs.iter() {
                let mut implementation_states = self
                    .implementation
                    .enabled_edges(pair.implementation(), output)
                    .peekable();

                if implementation_states.peek().is_none() {
                    continue;
                }

                todo!()
                /*states.push(Box::new(Itertools::cartesian_product(
                    implementation_states,
                    vec![pair.specification()].into_iter(),
                )));*/
            }

            for states_iter in states {
                for (implementation_state, specification_state) in states_iter {
                    let mut explored = true;

                    if !implementation_passed.contains(&implementation_state) {
                        implementation_passed.insert(&implementation_state);
                        explored = false;
                    }

                    if !specification_passed.contains(&specification_state) {
                        specification_passed.insert(&specification_state);
                        explored = false;
                    }

                    if !explored {
                        match RefinementStatePair::from_states(
                            implementation_state,
                            specification_state,
                        ) {
                            Ok(state) => worklist.push_back(state),
                            Err(_) => return false,
                        }
                    }
                }
            }
        }

        true
    }
}
