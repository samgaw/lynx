//! Internal computation, proved without exporting it as a NIF.

/// Inverts a boolean.
pub fn invert(value: bool) -> bool {
    !value
}
