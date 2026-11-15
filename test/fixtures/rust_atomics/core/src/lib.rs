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

pub fn replace(counter: &AtomicU64, expected: u64, replacement: u64) -> Result<u64, u64> {
    counter.compare_exchange(expected, replacement, Ordering::SeqCst, Ordering::SeqCst)
}

/// Signed contents stored behind a mutex.
pub struct Balance {
    pub value: i64,
}

/// Applies a signed adjustment, preserving the balance on either overflow.
pub fn adjust(balance: &mut Balance, delta: i64) -> bool {
    match balance.value.checked_add(delta) {
        Some(value) => {
            balance.value = value;
            true
        }
        None => false,
    }
}

/// Records how a receive operation completed.
#[derive(Debug)]
pub enum CompletionKind {
    Exact,
    Resumed { checkpoint: u64 },
}

/// Keeps the completed byte count and its protocol state together.
#[derive(Debug)]
pub struct Completion {
    pub bytes: [u8; 8],
    pub kind: CompletionKind,
}

/// Native receive state; completion and rejection are terminal.
pub enum Phase {
    Ready,
    Receiving { limit: u64, used: u64 },
    Complete(Completion),
    Rejected(u8),
}

/// Starts a bounded receive operation; an empty budget is already terminal.
pub fn start_phase(budget: u64) -> Phase {
    if budget == 0 {
        Phase::Ready
    } else {
        Phase::Receiving {
            limit: budget,
            used: 0,
        }
    }
}

/// Accounts for one chunk without wrapping; excess input rejects the operation.
pub fn consume_phase(phase: &mut Phase, amount: u64) -> bool {
    match phase {
        Phase::Ready | Phase::Complete(_) | Phase::Rejected(_) => false,
        Phase::Receiving { limit, used } => match used.checked_add(amount) {
            Some(total) if total < *limit => {
                *used = total;
                true
            }
            Some(total) if total == *limit => {
                *phase = Phase::Complete(Completion {
                    bytes: total.to_le_bytes(),
                    kind: CompletionKind::Exact,
                });
                true
            }
            _ => {
                *phase = Phase::Rejected(1);
                false
            }
        },
    }
}

/// Returns successful progress; a rejected operation has no accepted result.
pub fn phase_total(phase: &Phase) -> u64 {
    match phase {
        Phase::Receiving { used, .. } => *used,
        Phase::Complete(completion) => u64::from_le_bytes(completion.bytes),
        _ => 0,
    }
}

/// Counts the stored protocol bytes without changing their order.
pub fn buffer_length(bytes: &[u8]) -> usize {
    bytes.len()
}

/// Reads the leading protocol byte, using zero for an empty buffer.
#[expect(
    clippy::get_first,
    reason = "Exercise checked SliceIndex dispatch with a live resource owner"
)]
pub fn buffer_head(bytes: &[u8]) -> u8 {
    match bytes.get(0) {
        Some(first) => *first,
        None => 0,
    }
}

/// Appends borrowed protocol bytes while retaining the existing prefix.
pub fn append_bytes(output: &mut Vec<u8>, input: &[u8]) {
    output.extend_from_slice(input);
}

/// Consumes the mutex and retains the owned bytes even if a prior owner panicked.
pub fn take_bytes(bytes: std::sync::Mutex<Vec<u8>>) -> Vec<u8> {
    match bytes.into_inner() {
        Ok(value) => value,
        Err(error) => error.into_inner(),
    }
}

/// First-party protocol state with owning buffer cleanup captured by the compiler.
pub struct BufferState {
    pub bytes: Vec<u8>,
}

#[cfg(test)]
mod byte_handoff_tests {
    use super::take_bytes;
    use std::sync::Mutex;

    #[test]
    fn takes_unpoisoned_contents() {
        assert_eq!(take_bytes(Mutex::new(vec![1, 2, 255])), vec![1, 2, 255]);
    }

    #[test]
    fn poison_recovery_keeps_mutations_before_panic() {
        let bytes = Mutex::new(vec![1, 2]);
        assert!(std::panic::catch_unwind(|| {
            let mut guard = bytes.lock().unwrap();
            guard.push(9);
            panic!("poison the mutex after mutation");
        })
        .is_err());
        assert!(bytes.is_poisoned());
        assert_eq!(take_bytes(bytes), vec![1, 2, 9]);
    }
}
