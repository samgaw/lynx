//! Shared state transitions used by the resource and async extraction probes.

/// Counter contents stored behind the native lock.
pub struct Counter {
    /// Current counter value.
    pub value: u64,
}

/// Updates through an exclusive borrow; overflow leaves the original value intact.
pub fn increment(counter: &mut Counter, amount: u64) -> bool {
    match counter.value.checked_add(amount) {
        Some(value) => {
            counter.value = value;
            true
        }
        None => false,
    }
}

/// A named payload whose representation composes a flag and another workspace type.
pub struct Snapshot {
    /// Whether the snapshot is enabled.
    pub enabled: bool,
    /// Snapshot contents.
    pub counter: Counter,
}
