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
        assert_eq!(pairs(&table), vec![(1, 30), (2, 20)]);
        assert_eq!(pairs(&BTreeMap::new()), Vec::<(u64, u64)>::new());
        assert_eq!(first_key(&table), Some(1));
        assert_eq!(peek(&table, 1), Some(30));
        assert_eq!(peek(&table, 3), None);
        assert_eq!(take(&mut table, 3), None);
        assert_eq!(take(&mut table, 1), Some(30));
        assert_eq!(take(&mut table, 1), None);
        assert_eq!(peek(&table, 2), Some(20));
        assert_eq!(first_key(&table), Some(2));
        assert_eq!(first_key(&BTreeMap::new()), None);
        let mutex = std::sync::Mutex::new(table.clone());
        assert_eq!(locked_first_key(&mutex), Some(2));
        assert_eq!(locked_pairs(&mutex), vec![(2, 20)]);
        assert_eq!(*mutex.lock().unwrap(), table);
        assert!(contains(&values, 1));
        assert!(!release(&mut values, 3));
        assert!(release(&mut values, 1));
        assert!(!contains(&values, 1));
        assert!(!release(&mut values, 1));
        assert!(contains(&values, 2));
    }
}

/// An owned scalar snapshot of an ordered map entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Entry {
    pub key: u64,
    pub value: u64,
}

/// Copies every key/value pair in the map's iteration order.
pub fn entries(table: &BTreeMap<u64, u64>) -> Vec<Entry> {
    let mut output = Vec::new();
    for (key, value) in table {
        output.push(Entry {
            key: *key,
            value: *value,
        });
    }
    output
}

/// Copies every claimed key in the set's iteration order.
pub fn members(values: &BTreeSet<u64>) -> Vec<u64> {
    let mut output = Vec::new();
    for value in values {
        output.push(*value);
    }
    output
}

/// Replaces one entry while holding the registry lock, recovering poison.
///
/// # Panics
/// Recursive acquisition may panic or block and is outside the supported model.
pub fn locked_replace(
    table: &std::sync::Mutex<BTreeMap<u64, u64>>,
    key: u64,
    value: u64,
) -> Option<u64> {
    let mut guard = match table.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let previous = replace_value(&mut guard, key, value);
    drop(guard);
    previous
}

/// Removes one entry while holding the registry lock, recovering poison.
///
/// # Panics
/// Recursive acquisition may panic or block and is outside the supported model.
pub fn locked_take(table: &std::sync::Mutex<BTreeMap<u64, u64>>, key: u64) -> Option<u64> {
    let mut guard = match table.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let previous = take(&mut guard, key);
    drop(guard);
    previous
}

/// Claims one key while holding the set lock, recovering poison.
///
/// # Panics
/// Recursive acquisition may panic or block and is outside the supported model.
pub fn locked_claim(values: &std::sync::Mutex<BTreeSet<u64>>, key: u64) -> bool {
    let mut guard = match values.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let claimed = claim(&mut guard, key);
    drop(guard);
    claimed
}

/// Copies the first key in the map's ascending iteration order.
pub fn first_key(table: &BTreeMap<u64, u64>) -> Option<u64> {
    IntoIterator::into_iter(table).next().map(|(key, _)| *key)
}

/// Observes the first key while holding the map lock, recovering poison.
///
/// # Panics
/// Recursive acquisition may panic or block and is outside the supported model.
pub fn locked_first_key(table: &std::sync::Mutex<BTreeMap<u64, u64>>) -> Option<u64> {
    let guard = match table.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let first = first_key(&guard);
    drop(guard);
    first
}

/// Copies every map pair in ascending key order into an ordinary owned snapshot.
pub fn pairs(table: &BTreeMap<u64, u64>) -> Vec<(u64, u64)> {
    let mut output = Vec::new();
    for (key, value) in table {
        output.push((*key, *value));
    }
    output
}

/// Copies all map pairs while holding the map lock, recovering poison.
///
/// # Panics
/// Recursive acquisition may panic or block and is outside the supported model.
pub fn locked_pairs(table: &std::sync::Mutex<BTreeMap<u64, u64>>) -> Vec<(u64, u64)> {
    let guard = match table.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let snapshot = pairs(&guard);
    drop(guard);
    snapshot
}
