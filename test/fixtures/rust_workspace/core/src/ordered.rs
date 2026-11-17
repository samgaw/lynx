//! Scalar ordered collection operations shared by workspace callers.
use std::collections::{BTreeMap, BTreeSet};

/// Replaces a value while returning the previous value of the same key.
pub fn replace_value(table: &mut BTreeMap<u64, u64>, key: u64, value: u64) -> Option<u64> {
    table.insert(key, value)
}

/// Claims a key exactly once in an ordered set.
pub fn claim(values: &mut BTreeSet<u64>, key: u64) -> bool {
    values.insert(key)
}

/// Looks up a copied value without changing the table.
pub fn peek(table: &BTreeMap<u64, u64>, key: u64) -> Option<u64> {
    table.get(&key).copied()
}

/// Removes a key and returns its previous value.
pub fn take(table: &mut BTreeMap<u64, u64>, key: u64) -> Option<u64> {
    table.remove(&key)
}

/// Observes whether a key has been claimed.
pub fn contains(values: &BTreeSet<u64>, key: u64) -> bool {
    values.contains(&key)
}

/// Releases a claim and reports whether it existed.
pub fn release(values: &mut BTreeSet<u64>, key: u64) -> bool {
    values.remove(&key)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replacement_and_claims_preserve_unrelated_keys() {
        let mut table = BTreeMap::new();
        assert_eq!(replace_value(&mut table, 1, 10), None);
        assert_eq!(replace_value(&mut table, 2, 20), None);
        assert_eq!(replace_value(&mut table, 1, 30), Some(10));
        assert_eq!(table.get(&2), Some(&20));
        let mut values = BTreeSet::new();
        assert!(claim(&mut values, 1));
        assert!(claim(&mut values, 2));
        assert!(!claim(&mut values, 1));
        assert_eq!(values.len(), 2);
        assert_eq!(peek(&table, 1), Some(30));
        assert_eq!(peek(&table, 3), None);
        assert_eq!(take(&mut table, 3), None);
        assert_eq!(take(&mut table, 1), Some(30));
        assert_eq!(take(&mut table, 1), None);
        assert_eq!(peek(&table, 2), Some(20));
        assert!(contains(&values, 1));
        assert!(!release(&mut values, 3));
        assert!(release(&mut values, 1));
        assert!(!contains(&values, 1));
        assert!(!release(&mut values, 1));
        assert!(contains(&values, 2));
    }
}
