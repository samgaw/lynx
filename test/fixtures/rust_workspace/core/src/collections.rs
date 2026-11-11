//! In-place collection transitions that do not allocate or destroy elements.

/// A collection whose elements are only borrowed by length observations.
#[derive(Debug)]
pub struct Batch<T> {
    /// Stored values, with ownership retained by the caller.
    pub values: Vec<T>,
}

/// Observes length without decoding, moving or destroying an element.
pub fn batch_length<T>(input: &Batch<T>) -> usize {
    input.values.len()
}

/// Classifies a protocol outcome while releasing any owned diagnostic text.
pub fn result_is_ok(input: Result<u64, String>) -> bool {
    input.is_ok()
}

/// Replaces the first byte, leaving an empty input unchanged.
pub fn replace_slice_first(input: &mut [u8], value: u8) -> bool {
    if input.is_empty() {
        false
    } else {
        input[0] = value;
        true
    }
}

/// Applies the same transition through a vector's mutable slice view.
pub fn replace_first(mut input: Vec<u8>, value: u8) -> (bool, Vec<u8>) {
    let changed = replace_slice_first(input.as_mut_slice(), value);
    (changed, input)
}

/// Observes the shared slice view and returns ownership to the caller.
pub fn slice_length(input: Vec<u8>) -> (usize, Vec<u8>) {
    let slice: &[u8] = &input;
    (slice.len(), input)
}

/// Replaces one byte using Rust's bounds-checked mutable indexing.
///
/// # Panics
/// Panics when the position is outside the slice.
pub fn replace_at(input: &mut [u8], position: usize, value: u8) {
    input[position] = value;
}

/// Replaces the first signed protocol value without changing the remaining fields.
pub fn replace_slice_first_i64(input: &mut [i64], value: i64) -> bool {
    if input.is_empty() {
        false
    } else {
        input[0] = value;
        true
    }
}

/// Retains ownership while updating the first signed protocol value.
pub fn replace_first_i64(mut input: Vec<i64>, value: i64) -> (bool, Vec<i64>) {
    let changed = replace_slice_first_i64(input.as_mut_slice(), value);
    (changed, input)
}

/// Borrows an indexed element, returning None beyond the slice boundary.
pub fn lookup<T>(input: &[T], position: usize) -> Option<&T> {
    input.get(position)
}

/// Borrows a vector element through its standard indexing implementation.
///
/// # Panics
/// Panics when the position is outside the vector.
#[expect(clippy::ptr_arg, reason = "Exercise standard Vec indexing metadata")]
pub fn vector_at<T>(input: &Vec<T>, position: usize) -> &T {
    &input[position]
}

#[cfg(test)]
mod tests {
    use super::{replace_at, replace_first, slice_length};

    #[test]
    fn mutation_preserves_tail_length_and_allocation() {
        let input = vec![1, 2, 3];
        let pointer = input.as_ptr();
        let capacity = input.capacity();
        let (changed, input) = replace_first(input, 9);
        assert!(changed);
        assert_eq!(input, [9, 2, 3]);
        assert_eq!(input.as_ptr(), pointer);
        assert_eq!(input.capacity(), capacity);
        let (length, input) = slice_length(input);
        assert_eq!(length, 3);
        assert_eq!(input.as_ptr(), pointer);
        assert_eq!(replace_first(Vec::new(), 9), (false, Vec::new()));
    }

    #[test]
    #[should_panic]
    fn index_outside_slice_panics() {
        replace_at(&mut [1, 2], 2, 9);
    }
}
