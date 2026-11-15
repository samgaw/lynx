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

/// Observes the low-level protocol byte count across the crate boundary.
pub fn buffer_length(bytes: &[u8]) -> usize {
    atomic_core::buffer_length(bytes)
}

/// Delegates the checked byte observation to the low-level implementation.
pub fn buffer_head(bytes: &[u8]) -> u8 {
    atomic_core::buffer_head(bytes)
}

/// Copies borrowed protocol bytes into an independently owned buffer.
pub fn copy_bytes(input: &[u8]) -> Vec<u8> {
    let mut output = Vec::new();
    atomic_core::append_bytes(&mut output, input);
    output
}

/// Appends through the actual shared guard, including poison recovery.
///
/// # Panics
/// Recursive acquisition may panic or block and is outside this fixture.
pub fn locked_append(bytes: &std::sync::Mutex<Vec<u8>>, input: &[u8]) -> usize {
    let mut guard = match bytes.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    atomic_core::append_bytes(&mut guard, input);
    let length = guard.len();
    drop(guard);
    length
}

/// Hands the fully updated buffer back to its owner after releasing the guard.
///
/// # Panics
/// Shares the acquisition restrictions of [`locked_append`].
pub fn copy_locked(input: &[u8]) -> Vec<u8> {
    let bytes = std::sync::Mutex::new(Vec::new());
    locked_append(&bytes, input);
    atomic_core::take_bytes(bytes)
}

/// Appends through the shared current state and returns its committed length.
///
/// # Panics
/// Recursive acquisition may panic or block and is outside this fixture.
pub fn append_state(state: &std::sync::Mutex<atomic_core::BufferState>, input: &[u8]) -> u64 {
    let mut guard = match state.lock() {
        Ok(value) => value,
        Err(error) => error.into_inner(),
    };
    atomic_core::append_bytes(&mut guard.bytes, input);
    let length = guard.bytes.len() as u64;
    drop(guard);
    length
}

/// Reads shared state under the same mutex without clearing poison.
///
/// # Panics
/// Recursive acquisition may panic or block and is outside this fixture.
pub fn read_state(state: &std::sync::Mutex<atomic_core::BufferState>) -> (u64, u8) {
    let guard = match state.lock() {
        Ok(value) => value,
        Err(error) => error.into_inner(),
    };
    let result = (
        guard.bytes.len() as u64,
        atomic_core::buffer_head(&guard.bytes),
    );
    drop(guard);
    result
}

/// Consumes the mutex and its first-party owning payload without Rustler.
pub fn dispose_state(state: std::sync::Mutex<atomic_core::BufferState>) {
    drop(state);
}

#[cfg(test)]
mod locked_buffer_tests {
    use super::{copy_locked, locked_append};
    use std::sync::Mutex;

    #[test]
    fn reuses_the_current_contents_after_unlock() {
        let bytes = Mutex::new(vec![1, 2]);
        assert_eq!(locked_append(&bytes, &[3, 4]), 4);
        assert_eq!(locked_append(&bytes, &[5]), 5);
        assert_eq!(atomic_core::take_bytes(bytes), vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn preserves_raw_binary_values() {
        assert_eq!(copy_locked(&[0, 255, 128]), vec![0, 255, 128]);
        assert!(copy_locked(&[]).is_empty());
    }
}
