use std::collections::{HashSet, VecDeque};

use crate::automata::hyper_state_set::HyperStateSet;

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
pub struct Refinement {
    leader_follower: LeaderFollowers,
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
            Ok(state) => {
                visited.insert(&state);
                worklist.push_back(state);
            }
            Err(_) => return Err(()),
        }

        while let Some(state) = worklist.pop_front() {
            let mut channels: Vec<Vec<Option<Channel>>> = Vec::new();

            // Rule 1 (Common inputs): Both the specification and implementaion can react on the input.
            // Whenever t -i?->ᵀ t' for some t' ∈ Qᵀ and i? ∈ Actᵀᵢ ∩ Actᔆᵢ , then s -i?->ᔆ s' and (s', t') ∈ R for some s' ∈ Qᔆ
            for action in self.common_inputs.iter() {
                let channel = Some(action.input());
                channels.push(vec![channel, channel]);
            }

            // Rule 2 (Unique specification inputs): Only the specification reacts to the input.
            // Whenever t -i?->ᵀ t' for some t' ∈ Qᵀ and i? ∈ Actᵀᵢ \ Actᔆᵢ, then (s, t') ∈ R.
            for action in self.unique_specification_inputs.iter() {
                let channel = Some(action.input());
                channels.push(vec![None, channel]);
            }

            // Rule 3 (Common outputs): Both the specification and implementaion can produce the output.
            // Whenever s -o!->ᔆ s' for some s' ∈ Qᔆ and o! ∈ Actᵀₒ ∩ Actᔆₒ then t -o!->ᵀ t' and (s', t') ∈ R for some t' ∈ Qᵀ
            for action in self.common_outputs.iter() {
                let channel = Some(action.output());
                channels.push(vec![channel, channel]);
            }

            // Rule 4 (Unique implementation outputs): Only the implementation can produce the output.
            // Whenever s -o!->ᔆ s' for some s' ∈ Qᔆ and o! ∈ Actᵀₒ \ Actᔆₒ, then (s', t) ∈ R.
            for action in self.unique_implementation_outputs.iter() {
                let channel = Some(action.output());
                channels.push(vec![channel, None]);
            }

            for channels in channels.into_iter() {
                for transition in self.enabled(&state, channels) {
                    let mut state = match self.leader_follower.transition(transition) {
                        Ok(state) => state,
                        Err(_) => return Err(()),
                    };

                    // Rule 5 (Delay): If the implementation can perform the delay so should the specification.
                    // Whenever s -d->ᔆ s' for some s' ∈ Qᔆ and d ∈ R≥0, then t -d->ᵀ t' and (s', t') ∈ R for some t' ∈ Qᵀ.
                    state = match self.delay(state) {
                        Ok(state) => state,
                        Err(_) => return Err(()),
                    };

                    if !visited.contains(&state) {
                        visited.insert(&state);
                        worklist.push_back(state);
                    }
                }
            }
        }

        return Ok(());
    }
}

impl HTIOTS for Refinement {
    fn initial_state(&self) -> HyperState {
        self.leader_follower.initial_state()
    }

    fn delay(&self, state: HyperState) -> Result<HyperState, ()> {
        self.leader_follower.delay(state)
    }

    fn discrete(
        &self,
        state: HyperState,
        traversals: Vec<Option<Traversal>>,
    ) -> Result<HyperState, ()> {
        self.leader_follower.discrete(state, traversals)
    }

    fn is_enabled(&self, transition: HyperTransition) -> Result<bool, ()> {
        self.leader_follower.is_enabled(transition)
    }

    fn is_valid(&self, state: &HyperState) -> Result<bool, ()> {
        self.leader_follower.is_valid(state)
    }

    fn enabled(&self, state: &HyperState, channels: Vec<Option<Channel>>) -> Vec<HyperTransition> {
        self.leader_follower.enabled(state, channels)
    }
}
