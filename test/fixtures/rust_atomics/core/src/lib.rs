use std::sync::atomic::{AtomicU64, Ordering};

pub fn claim(counter: &AtomicU64) -> u64 {
    counter.fetch_add(1, Ordering::SeqCst)
}

pub fn current(counter: &AtomicU64) -> u64 {
    counter.load(Ordering::SeqCst)
}

pub fn reset(counter: &AtomicU64, value: u64) {
    counter.store(value, Ordering::SeqCst);
}
