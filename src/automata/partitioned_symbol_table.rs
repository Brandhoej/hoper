use std::num::{NonZeroU32, NonZeroU64};

use dashmap::DashMap;
use symbol_table::SymbolTable;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PartitionedSymbol(NonZeroU64);

impl PartitionedSymbol {
    pub const fn new(partition: u32, symbol: NonZeroU32) -> Self {
        Self(NonZeroU64::new(((partition as u64) << 32) | (symbol.get() as u64)).unwrap())
    }

    pub const fn partition(&self) -> u32 {
        (self.0.get() >> 32) as u32
    }

    pub const fn symbol(&self) -> NonZeroU32 {
        NonZeroU32::new((self.0.get() & 0xFFFF_FFFF) as u32).unwrap()
    }
}

pub struct PartitionedSymbolTable {
    tables: DashMap<u32, SymbolTable>,
}

impl PartitionedSymbolTable {
    pub fn new() -> Self {
        Self {
            tables: DashMap::new(),
        }
    }

    pub fn intern(&self, partition: u32, string: &str) -> PartitionedSymbol {
        let table_entry = self
            .tables
            .entry(partition)
            .or_insert_with(SymbolTable::new);
        let symbol = table_entry.intern(string);
        PartitionedSymbol::new(partition, symbol.into())
    }

    pub fn resolve(&self, ps: PartitionedSymbol) -> &str {
        let binding = self
            .tables
            .get(&ps.partition())
            .expect("unknown symbol partition");
        let str = binding.resolve(ps.symbol().into());
        unsafe { &*(str as *const str) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_intern_resolve() {
        let table = PartitionedSymbolTable::new();
        let sym1 = table.intern(1, "hello");
        let sym2 = table.intern(1, "world");

        assert_eq!(table.resolve(sym1), "hello");
        assert_eq!(table.resolve(sym2), "world");
    }

    #[test]
    fn test_intern_same_string() {
        let table = PartitionedSymbolTable::new();
        let sym1 = table.intern(42, "foo");
        let sym2 = table.intern(42, "foo");

        assert_eq!(sym1, sym2);
        assert_eq!(table.resolve(sym1), "foo");
    }

    #[test]
    fn test_intern_different_partitions() {
        let table = PartitionedSymbolTable::new();
        let sym1 = table.intern(1, "foo");
        let sym2 = table.intern(2, "foo");

        assert_ne!(sym1, sym2);
        assert_eq!(table.resolve(sym1), "foo");
        assert_eq!(table.resolve(sym2), "foo");
    }

    #[test]
    fn test_partitioned_symbol_accessors() {
        let inner_sym = NonZeroU32::new(123).unwrap();
        let ps = PartitionedSymbol::new(10, inner_sym);
        assert_eq!(ps.partition(), 10);
        assert_eq!(ps.symbol().get(), 123);
    }

    #[test]
    fn test_concurrent_intern() {
        let table = Arc::new(PartitionedSymbolTable::new());
        let mut handles = Vec::new();

        for partition in 0..8u32 {
            let table = Arc::clone(&table);
            handles.push(thread::spawn(move || {
                let sym = table.intern(partition, "concurrent");
                (partition, table.resolve(sym).to_string(), sym)
            }));
        }

        for handle in handles {
            let (partition, resolved, symbol) = handle.join().unwrap();
            assert_eq!(resolved, "concurrent");
            assert_eq!(symbol.partition(), partition);
        }
    }
}
