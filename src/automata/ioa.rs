use std::collections::HashSet;

use dyn_clone::DynClone;

use super::{action::Action, channel::Channel};

pub trait IOA: DynClone {
    fn inputs(&self) -> HashSet<Action>;
    fn outputs(&self) -> HashSet<Action>;
    fn actions(&self) -> HashSet<Action> {
        let mut actions = self.inputs();
        actions.extend(self.outputs());
        actions
    }
    fn channels(&self) -> Vec<Channel> {
        let mut channels = Vec::new();
        for input in self.inputs() {
            channels.push(Channel::new_input(input));
        }
        for output in self.outputs() {
            channels.push(Channel::new_output(output));
        }

        channels
    }
    fn channel(&self, action: Action) -> Option<Channel> {
        if self.inputs().contains(&action) {
            return Some(Channel::new_input(action));
        } else if self.outputs().contains(&action) {
            return Some(Channel::new_output(action));
        }
        return None;
    }
}

dyn_clone::clone_trait_object!(IOA);
