use std::collections::{HashSet, VecDeque};

use itertools::Itertools;

use crate::automata::{
    hyper_state_set::HyperStateSet,
    tiots::{Transition, TIOTS},
};

use super::{
    action::Action,
    channel::Channel,
    htiots::{HyperState, HyperTransition, HTIOTS},
    ioa::IOA,
    leader_followers::LeaderFollowers,
    specification::Specification,
    tioa::Traversal,
};

/// S ≤ T where S is the implementation and T is the specification.
/// Both are required to be specifications however by conventions the names can be confusing.
pub struct RefinementRelation {
    leader_follower: LeaderFollowers,
    common_inputs: HashSet<Action>,
    common_outputs: HashSet<Action>,
    unique_specification_inputs: HashSet<Action>,
    unique_implementation_outputs: HashSet<Action>,
}

impl RefinementRelation {
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

        // When the implementation can delay the specification should follow.
        // If it is impossible for the specification to follow then the implementation can
        // in the instance be "slower" than the specification and the delay returns an error.
        let leader_follower = LeaderFollowers::new(vec![implementation, specification], 0);

        Ok(Self {
            leader_follower,
            common_inputs,
            common_outputs,
            unique_specification_inputs,
            unique_implementation_outputs,
        })
    }

    pub fn common_inputs(&self) -> impl Iterator<Item = &Action> {
        self.common_inputs.iter()
    }

    pub fn common_outputs(&self) -> impl Iterator<Item = &Action> {
        self.common_outputs.iter()
    }

    pub fn unique_specification_inputs(&self) -> impl Iterator<Item = &Action> {
        self.unique_specification_inputs.iter()
    }

    pub fn unique_implementation_outputs(&self) -> impl Iterator<Item = &Action> {
        self.unique_implementation_outputs.iter()
    }

    pub fn implementation(&self) -> Box<&Specification> {
        todo!()
    }

    pub fn specification(&self) -> Box<&Specification> {
        todo!()
    }

    pub fn refines(&self) -> Result<(), ()> {
        // TODO: Use crossbeam to multi-thread the refinment check.
        // An example where work is shared between threads can be seen here:
        // https://docs.rs/crossbeam/latest/crossbeam/deque/index.html

        let mut worklist: VecDeque<HyperState> = VecDeque::new();
        let mut visited: HyperStateSet = HyperStateSet::new();

        // (qᔆ₀, qᵀ₀) ∈ R
        match self.delay(self.initial_state()) {
            Ok(state) => worklist.push_back(state),
            Err(_) => return Err(()),
        }

        while let Some(state) = worklist.pop_front() {
            let implementation_state = &state[0];
            let specification_state = &state[1];

            let mut products: Vec<Box<dyn Iterator<Item = (Transition, Transition)>>> =
                Vec::with_capacity(4);

            // Rule 1 (Common inputs): Both the specification and implementaion can react on the input.
            // Whenever t -i?->ᵀ t' for some t' ∈ Qᵀ and i? ∈ Actᵀᵢ ∩ Actᔆᵢ , then s -i?->ᔆ s' and (s', t') ∈ R for some s' ∈ Qᔆ
            for action in self.common_inputs.iter() {
                let channel = action.input();
                let mut specification_states = self
                    .specification()
                    .enabled(specification_state, &channel)
                    .into_iter()
                    .peekable();

                let mut implementation_states = self
                    .implementation()
                    .enabled(implementation_state, &channel)
                    .into_iter()
                    .peekable();

                // I believe that since both are specifications then thet must both be input-enabled.
                // Because of this of this, they would all in all states be able to react to all inputs.
                assert!(specification_states.peek().is_some());
                assert!(implementation_states.peek().is_some());

                products.push(Box::new(
                    implementation_states.cartesian_product(specification_states),
                ));
            }
        }

        todo!()
    }
}

impl HTIOTS for RefinementRelation {
    fn initial_state(&self) -> HyperState {
        self.leader_follower.initial_state()
    }

    fn delay(&self, state: HyperState) -> Result<HyperState, ()> {
        self.leader_follower.delay(state)
    }

    fn discrete(&self, state: HyperState, traversals: Vec<Traversal>) -> Result<HyperState, ()> {
        self.leader_follower.discrete(state, traversals)
    }

    fn is_enabled(&self, transition: HyperTransition) -> Result<bool, ()> {
        self.leader_follower.is_enabled(transition)
    }

    fn enabled(&self, state: &HyperState, channels: Vec<Channel>) -> Vec<HyperTransition> {
        self.leader_follower.enabled(state, channels)
    }
}
