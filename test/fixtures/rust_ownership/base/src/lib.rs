//! Owned values with observable destruction.

/// Tries acquisition first, retaining the owned guard in either acquired result.
///
/// # Panics
/// Recursive fallback to blocking acquisition can panic or deadlock.
pub fn acquire_or_wait(
    mutex: &std::sync::Mutex<bool>,
) -> std::sync::LockResult<std::sync::MutexGuard<'_, bool>> {
    match mutex.try_lock() {
        Ok(guard) => Ok(guard),
        Err(std::sync::TryLockError::Poisoned(error)) => Err(error),
        Err(std::sync::TryLockError::WouldBlock) => mutex.lock(),
    }
}

/// Toggles protected contents if an immediate acquisition succeeds.
/// A contended attempt leaves the protected contents unchanged.
pub fn try_toggle(mutex: &std::sync::Mutex<bool>) -> bool {
    let mut guard = match mutex.try_lock() {
        Ok(guard) => guard,
        Err(std::sync::TryLockError::Poisoned(error)) => error.into_inner(),
        Err(std::sync::TryLockError::WouldBlock) => return false,
    };
    toggle(&mut guard);
    drop(guard);
    true
}

/// A value whose destructor validates its code.
#[derive(Debug)]
pub struct Audit {
    /// Code checked at destruction.
    pub code: u64,
}
impl Drop for Audit {
    fn drop(&mut self) {
        assert!(self.code != 7);
    }
}
/// Consumes a value and executes its destructor.
///
/// # Panics
/// Propagates a panic from the value's destructor.
pub fn consume<T>(_value: T) {}

/// A scope guard that updates the original borrowed flag at destruction.
#[derive(Debug)]
pub struct Flip<'a>(pub &'a mut bool);

impl Drop for Flip<'_> {
    fn drop(&mut self) {
        *self.0 = !*self.0;
    }
}

/// Flips the borrowed flag by executing the guard's actual destructor.
pub fn flip(value: &mut bool) {
    let _guard = Flip(value);
}

/// Flips the borrowed flag on both normal exit and panic.
///
/// # Panics
/// Panics when `accepted` is false, running the guard's destructor.
pub fn checked_flip(value: &mut bool, accepted: bool) {
    let _guard = Flip(value);
    assert!(accepted);
}

/// Mutates protected contents before checking the request.
///
/// # Panics
/// Panics after mutation when the request is rejected.
pub fn mutate_before_check(value: &mut bool, accepted: bool) {
    *value = !*value;
    assert!(accepted);
}

/// Toggles a borrowed flag without panicking.
pub fn toggle(value: &mut bool) {
    *value = !*value;
}

/// Tries an exclusive update, preserving state when any lease conflicts.
pub fn try_rw_toggle(lock: &std::sync::RwLock<bool>) -> bool {
    let mut guard = match lock.try_write() {
        Ok(guard) => guard,
        Err(std::sync::TryLockError::Poisoned(error)) => error.into_inner(),
        Err(std::sync::TryLockError::WouldBlock) => return false,
    };
    toggle(&mut guard);
    drop(guard);
    true
}

/// Returns acquisition success and the shared value, recovering poisoned leases.
pub fn try_rw_read(lock: &std::sync::RwLock<bool>) -> (bool, bool) {
    let guard = match lock.try_read() {
        Ok(guard) => guard,
        Err(std::sync::TryLockError::Poisoned(error)) => error.into_inner(),
        Err(std::sync::TryLockError::WouldBlock) => return (false, false),
    };
    let value = *guard;
    drop(guard);
    (true, value)
}
