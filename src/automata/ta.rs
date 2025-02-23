use std::collections::HashSet;

use dyn_clone::DynClone;

use crate::zones::constraint::Clock;

use super::partitioned_symbol_table::PartitionedSymbol;

pub trait TA: DynClone {
    fn clock_count(&self) -> Clock;
    fn clocks(&self) -> HashSet<PartitionedSymbol>;
}

dyn_clone::clone_trait_object!(TA);
