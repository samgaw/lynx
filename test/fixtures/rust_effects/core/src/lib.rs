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

/// Consumes the transferred native owner before checking the request.
///
/// # Panics
/// Panics when `accepted` is false, after native destruction has completed.
pub fn release_checked(mutex: std::sync::Mutex<u64>, accepted: bool) {
    drop(mutex);
    assert!(accepted);
}

/// Uses compiler-generated unwind cleanup when the request is rejected.
///
/// # Panics
/// Panics when `accepted` is false, destroying the owned mutex during unwind.
pub fn assert_then_release(mutex: std::sync::Mutex<u64>, accepted: bool) {
    assert!(accepted);
    drop(mutex);
}
