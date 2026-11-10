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
