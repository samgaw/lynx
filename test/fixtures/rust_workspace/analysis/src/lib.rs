pub fn analyse(value: i64) -> Option<i64> {
    experiment_core::evaluate(value)?.checked_add(1)
}

/// Composes two calls to the first-party core crate.
pub fn restore(value: bool) -> bool {
    experiment_core::invert(experiment_core::invert(value))
}

/// Composes fixed-width arithmetic across the first-party crate boundary.
///
/// # Panics
/// Panics on overflow when the Cargo profile enables overflow checks.
pub fn twice_plus_one(value: i64) -> i64 {
    experiment_core::double(value) + 1
}

/// Composes shared structs and enums into a standard Rust result.
pub fn classify(value: (bool, i64)) -> Result<i64, u8> {
    let reading = experiment_core::Reading {
        enabled: value.0,
        value: value.1,
    };
    match experiment_core::decide(reading) {
        experiment_core::Decision::Accept(value) => Ok(value),
        experiment_core::Decision::Reject(code) => Err(code),
    }
}

/// Delegates tuple computation to another first-party crate.
pub fn transform_pair(value: (bool, i64)) -> (bool, i64) {
    experiment_core::transform_pair(value)
}

/// Composes a representation-independent operation across the workspace.
pub fn preserve<T>(value: T) -> T {
    experiment_core::preserve(value)
}

/// Returns the number of bytes in an immutable slice.
pub fn byte_length(value: &[u8]) -> u64 {
    experiment_core::byte_length(value)
}
