//! Composition across a first-party Cargo dependency.

/// Restores the input by composing two inversions.
pub fn restore(value: bool) -> bool {
    example_core::invert(example_core::invert(value))
}
