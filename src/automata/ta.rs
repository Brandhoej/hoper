use std::collections::HashSet;

use symbol_table::Symbol;

pub trait TA {
    fn clocks(&self) -> HashSet<Symbol>;
}
