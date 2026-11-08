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

/// Writes through a shared file handle, retaining partial-write and error results.
/// # Errors
/// Returns the operating system's write error without replacing the handle.
pub fn write_shared_file(file: &std::fs::File, bytes: &[u8]) -> std::io::Result<usize> {
    use std::io::Write;
    let mut borrowed = file;
    borrowed.write(bytes)
}

/// Reads once without hiding EOF, partial input or operating-system errors.
/// # Errors
/// Propagates the operating system's read error.
pub fn read_file_once(file: &mut std::fs::File, bytes: &mut [u8]) -> std::io::Result<usize> {
    use std::io::Read;
    file.read(bytes)
}

/// Parses a leading little-endian word; either missing byte rejects the input.
/// # Errors
/// Propagates the first read error without returning a parsed word.
pub fn read_file_word(file: &mut std::fs::File) -> std::io::Result<Option<u16>> {
    let mut first = [0u8];
    match read_file_once(file, &mut first) {
        Err(error) => Err(error),
        Ok(0) => Ok(None),
        Ok(_) => {
            let mut second = [0u8];
            match read_file_once(file, &mut second) {
                Err(error) => Err(error),
                Ok(0) => Ok(None),
                Ok(_) => {
                    let [low] = first;
                    let [high] = second;
                    Ok(Some(u16::from_le_bytes([low, high])))
                }
            }
        }
    }
}

/// Encodes a word and its complement for a fresh checked record.
pub fn encode_record(value: u16) -> [u8; 4] {
    let [low, high] = value.to_le_bytes();
    let [inverse_low, inverse_high] = (!value).to_le_bytes();
    [low, high, inverse_low, inverse_high]
}

/// Rejects an inconsistent word/complement pair.
pub fn decode_record(value: u16, inverse: u16) -> Option<u16> {
    if value ^ inverse == u16::MAX {
        Some(value)
    } else {
        None
    }
}

/// Reads a checked record, rejecting either incomplete word or a bad complement.
/// # Errors
/// Propagates the first read error without claiming an accepted record.
pub fn read_file_record(file: &mut std::fs::File) -> std::io::Result<Option<u16>> {
    match read_file_word(file) {
        Err(error) => Err(error),
        Ok(None) => Ok(None),
        Ok(Some(value)) => match read_file_word(file) {
            Err(error) => Err(error),
            Ok(None) => Ok(None),
            Ok(Some(inverse)) => Ok(decode_record(value, inverse)),
        },
    }
}

/// Synchronizes the current directory and closes its owned descriptor on every return.
/// # Errors
/// Propagates errors from opening or synchronizing the directory.
pub fn synchronize_directory() -> std::io::Result<()> {
    let directory = std::fs::File::open(".")?;
    directory.sync_all()
}

#[cfg(test)]
mod shared_file_tests {
    #[test]
    fn shared_writes_advance_one_file_position() -> std::io::Result<()> {
        let path = std::env::temp_dir().join(format!("lynx-shared-write-{}", std::process::id()));
        let file = std::fs::File::create_new(&path)?;
        assert_eq!(super::write_shared_file(&file, &[1, 2])?, 2);
        assert_eq!(super::write_shared_file(&file, &[3])?, 1);
        file.sync_all()?;
        assert_eq!(std::fs::read(&path)?, [1, 2, 3]);
        drop(file);
        std::fs::remove_file(path)
    }
}
