use std::collections::HashSet;

use dyn_clone::DynClone;

use super::action::Action;

pub trait IOA: DynClone {
    fn inputs(&self) -> HashSet<Action>;
    fn outputs(&self) -> HashSet<Action>;
    fn actions(&self) -> HashSet<Action> {
        let mut actions = self.inputs();
        actions.extend(self.outputs());
        actions
    }
}

dyn_clone::clone_trait_object!(IOA);
