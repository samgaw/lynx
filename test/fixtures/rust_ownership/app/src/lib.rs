//! Cross-crate ownership composition.
/// Executes the base crate's generic consumer and actual destructor.
///
/// # Panics
/// Panics when the code is seven.
pub fn run(code: u64) {
    ownership_base::consume(ownership_base::Audit { code });
}

/// Consumes a scalar through the same generic compiler dictionary interface.
pub fn run_scalar(code: u64) {
    ownership_base::consume(code);
}

/// Observes a guard's mutation after a cross-crate borrowed call returns.
pub fn scoped_flip(mut value: bool) -> bool {
    ownership_base::flip(&mut value);
    value
}

/// Composes a fallible borrowed call with the caller's scope guard.
///
/// # Panics
/// Propagates rejection after updating both original borrowed flags.
pub fn compose(first: &mut bool, second: &mut bool, accepted: bool) {
    let _guard = ownership_base::Flip(second);
    ownership_base::checked_flip(first, accepted);
    *first = !*first;
}

/// Commits the borrowed transition and releases its standard-library guard.
///
/// # Panics
/// Rejection retains the mutation and poisons the mutex during release.
pub fn guard_panic(mut guard: std::sync::MutexGuard<'_, bool>, accepted: bool) {
    ownership_base::mutate_before_check(&mut guard, accepted);
}

/// Calls the actual borrowed transition without exposing native ownership.
///
/// # Panics
/// Rejection propagates after updating the borrowed value.
pub fn checked_value(value: &mut bool, accepted: bool) {
    ownership_base::mutate_before_check(value, accepted);
}

/// Acquires and disposes a local mutex around the composed guarded operation.
///
/// # Panics
/// Rejection unwinds both the held guard and its local mutex.
pub fn local_guard_panic(value: bool, accepted: bool) -> bool {
    let mutex = std::sync::Mutex::new(value);
    consume_guard_panic(mutex, accepted)
}

/// Recovers poisoned acquisition and consumes its owned mutex on either exit.
///
/// # Panics
/// Rejection retains the mutation until guard and mutex cleanup complete.
pub fn consume_guard_panic(mutex: std::sync::Mutex<bool>, accepted: bool) -> bool {
    let guard = match mutex.lock() {
        Ok(guard) => guard,
        Err(poisoned) => poisoned.into_inner(),
    };
    guard_panic(guard, accepted);
    true
}

/// Toggles a borrowed flag without panicking.
pub fn toggle(value: &mut bool) {
    ownership_base::toggle(value);
}

/// Preserves a held value on contention, then updates after releasing its guard.
pub fn try_cycle(value: bool) -> (bool, bool, bool, bool) {
    let mutex = std::sync::Mutex::new(value);
    let first = match mutex.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let rejected = ownership_base::try_toggle(&mutex);
    let unchanged = *first;
    drop(first);
    let accepted = ownership_base::try_toggle(&mutex);
    let last = match mutex.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let result = (rejected, unchanged, accepted, *last);
    drop(last);
    drop(mutex);
    result
}

/// Mutates a guard returned by another crate and observes its released contents.
pub fn returned_guard_flip(value: bool) -> bool {
    let mutex = std::sync::Mutex::new(value);
    let mut guard = match ownership_base::acquire_or_wait(&mutex) {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    ownership_base::toggle(&mut guard);
    drop(guard);
    let reader = match mutex.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let result = *reader;
    drop(reader);
    drop(mutex);
    result
}

#[cfg(test)]
mod tests {
    use super::{guard_panic, returned_guard_flip, try_cycle};
    use std::sync::Mutex;

    #[test]
    fn nonblocking_cycle_preserves_rejected_updates() {
        for initial in [false, true] {
            assert_eq!(try_cycle(initial), (false, initial, true, !initial));
        }
    }

    #[test]
    fn returned_guard_commits_before_readback() {
        for initial in [false, true] {
            assert_eq!(returned_guard_flip(initial), !initial);
        }
    }

    #[test]
    fn guarded_mutation_survives_panic_and_sets_poison() {
        for initial in [false, true] {
            for accepted in [false, true] {
                let mutex = Mutex::new(initial);
                let outcome = std::panic::catch_unwind(|| {
                    guard_panic(mutex.lock().unwrap(), accepted);
                });
                assert_eq!(outcome.is_ok(), accepted);
                match mutex.into_inner() {
                    Ok(value) => {
                        assert!(accepted);
                        assert_eq!(value, !initial);
                    }
                    Err(poisoned) => {
                        assert!(!accepted);
                        assert_eq!(poisoned.into_inner(), !initial);
                    }
                }
            }
        }
    }
}

/// Exercises both rejected lock modes and observes a cross-crate committed update.
pub fn try_rw_cycle(value: bool) -> (bool, bool, bool, bool) {
    let lock = std::sync::RwLock::new(value);
    let reader = match lock.read() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let rejected_write = ownership_base::try_rw_toggle(&lock);
    drop(reader);
    let writer = match lock.write() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let rejected_read = ownership_base::try_rw_read(&lock).0;
    drop(writer);
    let accepted = ownership_base::try_rw_toggle(&lock);
    let final_value = ownership_base::try_rw_read(&lock).1;
    #[expect(
        clippy::drop_non_drop,
        reason = "Ends the owned lock lifetime before returning the observations."
    )]
    drop(lock);
    (rejected_write, rejected_read, accepted, final_value)
}

#[cfg(test)]
mod try_rw_tests {
    #[test]
    fn rejected_attempts_preserve_then_commit() {
        for value in [false, true] {
            assert_eq!(super::try_rw_cycle(value), (false, false, true, !value));
        }
    }
}
