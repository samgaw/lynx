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
