use std::collections::HashSet;

use super::action::Action;

pub trait IOA {
    fn inputs(&self) -> HashSet<Action>;
    fn outputs(&self) -> HashSet<Action>;
    fn actions(&self) -> HashSet<Action> {
        let mut actions = self.inputs();
        actions.extend(self.outputs());
        actions
    }
}
