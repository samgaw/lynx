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
pub fn append_state(state: &std::sync::Mutex<ReceiveState>, input: &[u8]) -> u64 {
    let mut guard = match state.lock() {
        Ok(value) => value,
        Err(error) => error.into_inner(),
    };
    atomic_core::append_bytes(&mut guard.buffer.bytes, input);
    let length = guard.buffer.bytes.len() as u64;
    drop(guard);
    length
}

/// Reads shared state under the same mutex without clearing poison.
///
/// # Panics
/// Recursive acquisition may panic or block and is outside this fixture.
pub fn read_state(state: &std::sync::Mutex<ReceiveState>) -> (u64, u8) {
    let guard = match state.lock() {
        Ok(value) => value,
        Err(error) => error.into_inner(),
    };
    let result = (
        guard.buffer.bytes.len() as u64,
        atomic_core::buffer_head(&guard.buffer.bytes),
    );
    drop(guard);
    result
}

/// Consumes the mutex and its first-party owning payload without Rustler.
pub fn dispose_state(state: std::sync::Mutex<atomic_core::BufferState>) {
    drop(state);
}

/// Nested cross-crate owning state used by the shared Rustler resource.
pub struct ReceiveState {
    pub buffer: atomic_core::BufferState,
}

/// Consumes nested shared state independently of any NIF export.
pub fn dispose_receive_state(state: std::sync::Mutex<ReceiveState>) {
    drop(state);
}

/// Composes the actual first-party frame parser, including its input mutation.
pub fn take_frame(input: &mut Vec<u8>) -> Result<Option<Vec<u8>>, u8> {
    atomic_core::frames::take_frame(input)
}

/// Observes one extracted parse without exposing owned vectors as NIF arguments.
///
/// # Panics
/// Follows the standard allocator's failure policy.
pub fn frame_summary(input: &[u8]) -> (u8, u64, u64) {
    let mut bytes = copy_bytes(input);
    let (status, consumed) = match take_frame(&mut bytes) {
        Ok(Some(frame)) => (2, frame.len() as u64),
        Ok(None) => (0, 0),
        Err(error) => (error, 0),
    };
    (status, consumed, bytes.len() as u64)
}

/// Consumes one complete frame while holding the persistent receive-state guard.
/// Incomplete or malformed input leaves every buffered byte unchanged.
///
/// # Panics
/// Recursive acquisition may panic or block and is outside this fixture.
pub fn parse_frame(state: &std::sync::Mutex<ReceiveState>) -> (u8, u64, u64) {
    let mut guard = match state.lock() {
        Ok(value) => value,
        Err(error) => error.into_inner(),
    };
    let (status, consumed) = match atomic_core::frames::take_frame(&mut guard.buffer.bytes) {
        Ok(Some(frame)) => (2, frame.len() as u64),
        Ok(None) => (0, 0),
        Err(error) => (error, 0),
    };
    let remaining = guard.buffer.bytes.len() as u64;
    drop(guard);
    (status, consumed, remaining)
}

/// Parses before applying request policy, retaining any consumed input on failure.
///
/// # Panics
/// Rejection destroys the produced reply after the parser updated the buffer.
pub fn checked_frame(input: &mut Vec<u8>, accepted: bool) -> Result<Option<Vec<u8>>, u8> {
    let frame = atomic_core::frames::take_frame(input);
    atomic_core::accept_frame(accepted);
    frame
}

/// Releases a buffer guard on success and poisons it after request rejection.
///
/// # Panics
/// Rejection retains the parser's mutation before unwinding through the guard.
pub fn guard_frame(
    mut guard: std::sync::MutexGuard<'_, ReceiveState>,
    accepted: bool,
) -> Result<Option<Vec<u8>>, u8> {
    checked_frame(&mut guard.buffer.bytes, accepted)
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

#[cfg(test)]
mod frame_tests {
    use super::{append_state, parse_frame, read_state, ReceiveState};
    use std::sync::Mutex;

    fn empty() -> Mutex<ReceiveState> {
        Mutex::new(ReceiveState {
            buffer: atomic_core::BufferState { bytes: Vec::new() },
        })
    }

    #[test]
    fn consumes_successive_frames_and_releases_the_guard() {
        let state = empty();
        assert_eq!(append_state(&state, &[1, 0, 1, 7, 1, 0, 0]), 7);
        assert_eq!(parse_frame(&state), (2, 4, 3));
        assert_eq!(parse_frame(&state), (2, 3, 0));
        assert_eq!(read_state(&state), (0, 0));
    }

    #[test]
    fn retains_incomplete_and_malformed_bytes() {
        let state = empty();
        append_state(&state, &[1, 0, 2, 8]);
        assert_eq!(parse_frame(&state), (0, 0, 4));
        assert_eq!(read_state(&state), (4, 1));
        append_state(&state, &[9]);
        assert_eq!(parse_frame(&state), (2, 5, 0));
        append_state(&state, &[2, 0, 0]);
        assert_eq!(parse_frame(&state), (1, 0, 3));
        assert_eq!(read_state(&state), (3, 2));
    }

    #[test]
    fn poison_recovery_keeps_the_current_buffer() {
        let state = empty();
        append_state(&state, &[1, 0, 0]);
        let panic = std::panic::catch_unwind(|| {
            let _guard = state.lock().expect("fresh fixture mutex");
            panic!("poison the fixture mutex");
        });
        assert!(panic.is_err());
        assert_eq!(parse_frame(&state), (2, 3, 0));
        assert_eq!(read_state(&state), (0, 0));
        assert!(state.is_poisoned());
    }
}

#[cfg(test)]
mod captured_frame_tests {
    use super::{guard_frame, ReceiveState};
    use atomic_core::BufferState;
    use std::sync::Mutex;

    #[test]
    fn rejection_releases_and_poisons_the_updated_buffer() {
        let state = Mutex::new(ReceiveState {
            buffer: BufferState {
                bytes: vec![1, 0, 1, 255, 1, 0, 0],
            },
        });
        let rejected = std::panic::catch_unwind(|| guard_frame(state.lock().unwrap(), false));
        assert!(rejected.is_err());
        match state.lock() {
            Err(error) => assert_eq!(error.get_ref().buffer.bytes, vec![1, 0, 0]),
            Ok(_) => panic!("rejected frame must poison the mutex"),
        };
    }
}
