use std::collections::HashSet;

use symbol_table::Symbol;

use crate::zones::constraint::Clock;

pub trait TA {
    fn clock_count(&self) -> Clock;
    fn clocks(&self) -> HashSet<Symbol>;
}
