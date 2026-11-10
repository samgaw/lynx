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
