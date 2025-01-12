use std::collections::HashSet;

use symbol_table::Symbol;

pub trait IOA {
    fn inputs(&self) -> HashSet<Symbol>;
    fn outputs(&self) -> HashSet<Symbol>;
    fn actions(&self) -> HashSet<Symbol> {
        let mut actions = self.inputs();
        actions.extend(self.outputs());
        actions
    }
}
