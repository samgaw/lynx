use std::sync::atomic::AtomicU64;

pub fn claim_two(counter: &AtomicU64) -> (u64, u64) {
    let first = atomic_core::claim(counter);
    let second = atomic_core::claim(counter);
    (first, second)
}
