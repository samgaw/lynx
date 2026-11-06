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

/// Acquires shared counter state, retaining the guard in a poisoned result.
///
/// # Panics
/// Native recursive acquisition can panic or block; verification rejects it.
pub fn acquire_counter(
    mutex: &std::sync::Mutex<Counter>,
) -> std::sync::LockResult<std::sync::MutexGuard<'_, Counter>> {
    mutex.lock()
}

/// Reads the counter through a shared borrow of its held guard.
pub fn read_guard(guard: &std::sync::MutexGuard<'_, Counter>) -> u64 {
    guard.value
}

/// Composes the checked transition through an exclusive guard borrow.
pub fn increment_guard(guard: &mut std::sync::MutexGuard<'_, Counter>, amount: u64) -> bool {
    increment(guard, amount)
}

/// Commits the reconstructed guard payload by explicitly releasing ownership.
pub fn update_release(mut guard: std::sync::MutexGuard<'_, Counter>, amount: u64) -> bool {
    let changed = increment_guard(&mut guard, amount);
    drop(guard);
    changed
}

/// Releases a held guard without modifying its payload.
pub fn release_guard(guard: std::sync::MutexGuard<'_, Counter>) {
    drop(guard);
}

/// Commits through the compiler-generated guard destructor at scope exit.
pub fn update_scope(mut guard: std::sync::MutexGuard<'_, Counter>, amount: u64) -> bool {
    increment_guard(&mut guard, amount)
}
