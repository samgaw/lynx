use std::sync::atomic::AtomicU64;

pub fn claim_two(counter: &AtomicU64) -> (u64, u64) {
    let first = atomic_core::claim(counter);
    let second = atomic_core::claim(counter);
    (first, second)
}

pub fn try_set(counter: &AtomicU64, expected: u64, replacement: u64) -> (bool, u64) {
    match atomic_core::replace(counter, expected, replacement) {
        Ok(previous) => (true, previous),
        Err(observed) => (false, observed),
    }
}

/// Updates signed state through its actual lock guard and checked callee.
/// Poison recovery retains the acquired guard and its current contents.
///
/// # Panics
/// A recursive acquisition may panic or block and is outside this fixture.
pub fn locked_adjust(balance: &std::sync::Mutex<atomic_core::Balance>, delta: i64) -> (bool, i64) {
    let mut guard = match balance.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let changed = atomic_core::adjust(&mut guard, delta);
    let value = guard.value;
    drop(guard);
    (changed, value)
}

/// Applies a receive transition and observes its result under the same guard.
///
/// # Panics
/// Recursive acquisition may panic or block and is outside this fixture.
pub fn consume_locked(phase: &std::sync::Mutex<atomic_core::Phase>, amount: u64) -> (bool, u64) {
    let mut guard = match phase.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let accepted = atomic_core::consume_phase(&mut guard, amount);
    let total = atomic_core::phase_total(&guard);
    drop(guard);
    (accepted, total)
}
