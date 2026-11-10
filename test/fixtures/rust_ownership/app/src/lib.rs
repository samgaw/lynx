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

#[cfg(test)]
mod tests {
    use super::guard_panic;
    use std::sync::Mutex;

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
