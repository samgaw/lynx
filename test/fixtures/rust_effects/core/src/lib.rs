//! Shared state transitions used by the resource and async extraction probes.

/// Counter contents stored behind the native lock.
pub struct Counter {
    /// Current counter value.
    pub value: u64,
}

/// Reads shared counter contents without transferring ownership.
pub fn counter_value(counter: &Counter) -> u64 {
    counter.value
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

/// Retains ownership of a poisoned guard without clearing the poison flag.
pub fn recover_guard(
    acquired: std::sync::LockResult<std::sync::MutexGuard<'_, Counter>>,
) -> std::sync::MutexGuard<'_, Counter> {
    match acquired {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    }
}

/// Applies the checked transition under a complete native critical section.
///
/// # Panics
/// Recursive acquisition may panic or block; verification rejects that case.
pub fn locked_increment(mutex: &std::sync::Mutex<Counter>, amount: u64) -> bool {
    let guard = recover_guard(mutex.lock());
    update_release(guard, amount)
}

/// Performs a checked scalar update while retaining lock ownership through release.
///
/// # Panics
/// Recursive acquisition can panic or block; verification rejects that case.
pub fn locked_scalar_increment(mutex: &std::sync::Mutex<u64>, amount: u64) -> bool {
    let mut guard = match mutex.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let mut counter = Counter { value: *guard };
    let changed = increment(&mut counter, amount);
    *guard = counter.value;
    drop(guard);
    changed
}

/// Increments a scalar, preserving the fixed-width saturation bound.
pub fn saturating_increment(value: u64) -> u64 {
    value.saturating_add(1)
}

/// A first-party future whose progress is retained across explicit polls.
pub struct PausedCounter {
    /// Whether the next poll must suspend once.
    pub waiting: bool,
    /// The computation input retained while suspended.
    pub counter: Counter,
}

/// Constructs a future which returns Pending before computing its result.
pub fn paused_counter(value: u64) -> PausedCounter {
    PausedCounter {
        waiting: true,
        counter: Counter { value },
    }
}

impl std::future::Future for PausedCounter {
    type Output = u64;

    fn poll(
        self: std::pin::Pin<&mut Self>,
        context: &mut std::task::Context<'_>,
    ) -> std::task::Poll<u64> {
        let this = self.get_mut();
        if this.waiting {
            this.waiting = false;
            context.waker().wake_by_ref();
            std::task::Poll::Pending
        } else {
            std::task::Poll::Ready(saturating_increment(this.counter.value))
        }
    }
}

/// Synchronizes a borrowed regular file without changing its Rust ownership.
/// # Errors
/// Propagates the native synchronization error.
pub fn synchronize_file(file: &std::fs::File) -> std::io::Result<()> {
    file.sync_all()
}
