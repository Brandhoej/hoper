use std::collections::HashSet;

use crate::zones::constraint::Clock;

use super::partitioned_symbol_table::PartitionedSymbol;

pub trait TA {
    fn clock_count(&self) -> Clock;
    fn clocks(&self) -> HashSet<PartitionedSymbol>;
}
