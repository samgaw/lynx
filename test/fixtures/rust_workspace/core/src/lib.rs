pub mod collections;
pub mod protocol;

pub fn evaluate(value: i64) -> Option<i64> {
    value.checked_mul(2)
}

/// Negates a boolean without exporting it as a NIF.
pub fn invert(value: bool) -> bool {
    !value
}

/// Doubles a fixed-width signed integer.
///
/// # Panics
/// Panics on overflow when the Cargo profile enables overflow checks.
pub fn double(value: i64) -> i64 {
    value * 2
}

/// A first-party value shared with the analysis crate.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct Reading {
    /// Whether the reading should be accepted.
    pub enabled: bool,
    /// The signed payload preserved by classification.
    pub value: i64,
}

/// A first-party decision whose payload survives a cross-crate call.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Decision {
    /// An accepted reading and its original payload.
    Accept(i64),
    /// A rejected reading and its error code.
    Reject(u8),
}

/// Classifies a reading without exposing either type through Rustler.
pub fn decide(reading: Reading) -> Decision {
    if reading.enabled {
        Decision::Accept(reading.value)
    } else {
        Decision::Reject(7)
    }
}

/// Negates the flag while preserving a tuple's integer payload.
pub fn transform_pair(value: (bool, i64)) -> (bool, i64) {
    (!value.0, value.1)
}

/// Preserves an owned value without depending on its representation.
pub fn preserve<T>(value: T) -> T {
    value
}

/// Returns the number of bytes in an immutable slice.
pub fn byte_length(value: &[u8]) -> u64 {
    value.len() as u64
}

/// Uses the default flag when an optional protocol field is absent.
pub fn optional_flag(value: Option<bool>) -> bool {
    match value {
        Some(flag) => !flag,
        None => false,
    }
}
