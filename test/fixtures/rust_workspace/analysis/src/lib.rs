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

/// Parses a bounded frame through another first-party crate.
pub fn parse_frame(value: &[u8]) -> Result<u64, u8> {
    experiment_core::protocol::parse_frame(value)
}

/// Preserves detailed UTF-8 validation results across the crate boundary.
pub fn utf8_status(value: &[u8]) -> Result<u64, (u64, u8)> {
    experiment_core::protocol::utf8_status(value)
}

/// Composes both wire byte orders across a first-party crate boundary.
pub fn endian_roundtrip(value: u32) -> u32 {
    experiment_core::protocol::big_endian_roundtrip(
        experiment_core::protocol::little_endian_roundtrip(value),
    )
}

/// Reads a network header through the core crate's bounds check.
pub fn read_header(input: &[u8]) -> Option<u32> {
    experiment_core::protocol::read_header(input)
}

/// Delegates an in-place vector update across the first-party crate boundary.
pub fn replace_first(input: Vec<u8>, value: u8) -> (bool, Vec<u8>) {
    experiment_core::collections::replace_first(input, value)
}

/// Observes a vector through the core crate's shared view.
pub fn slice_length(input: Vec<u8>) -> (usize, Vec<u8>) {
    experiment_core::collections::slice_length(input)
}

/// Delegates a checked mutable index operation to the core crate.
pub fn replace_at(input: &mut [u8], position: usize, value: u8) {
    experiment_core::collections::replace_at(input, position, value);
}

/// Applies the core protocol flag policy across the workspace boundary.
pub fn optional_flag(value: Option<bool>) -> bool {
    experiment_core::optional_flag(value)
}

/// Applies the core update policy to a batch of signed protocol fields.
pub fn replace_first_i64(input: Vec<i64>, value: i64) -> (bool, Vec<i64>) {
    experiment_core::collections::replace_first_i64(input, value)
}

/// Uses the core ordering policy across the workspace boundary.
pub fn order_pair(left: u64, right: u64) -> (u64, u64) {
    experiment_core::order_pair(left, right)
}

/// Observes a generic batch through its first-party implementation.
pub fn batch_length<T>(input: &experiment_core::collections::Batch<T>) -> usize {
    experiment_core::collections::batch_length(input)
}

/// Composes classification and owned diagnostic cleanup across crates.
pub fn result_is_ok(input: Result<u64, String>) -> bool {
    experiment_core::collections::result_is_ok(input)
}

/// Preserves the core slice lookup result across the workspace boundary.
pub fn lookup<T>(input: &[T], position: usize) -> Option<&T> {
    experiment_core::collections::lookup(input, position)
}

/// Borrows an element through the low-level vector operation.
///
/// # Panics
/// Panics when the position is outside the vector.
pub fn vector_at<T>(input: &Vec<T>, position: usize) -> &T {
    experiment_core::collections::vector_at(input, position)
}

/// Composes an actual scalar-capturing callback across the workspace boundary.
pub fn masked_error(value: u64, mask: u64) -> Result<u64, u64> {
    experiment_core::mask_error(Err(value), mask)
}

/// Returns the borrowed payload length, or no value for a truncated payload.
pub fn prefix_length(input: &[u8], length: u8) -> Option<u64> {
    experiment_core::protocol::prefix(input, length).map(|payload| payload.len() as u64)
}

/// Separates a bounded payload from the exact unconsumed remainder.
pub fn split_payload(input: &[u8], position: usize) -> Option<(&[u8], &[u8])> {
    let payload = experiment_core::protocol::window(input, 0, position)?;
    let rest = experiment_core::protocol::remainder(input, position)?;
    Some((payload, rest))
}

/// Reports consumed and remaining lengths without exporting borrowed pointers.
pub fn split_lengths(input: &[u8], length: u8) -> Option<(u64, u64)> {
    split_payload(input, length as usize)
        .map(|(payload, rest)| (payload.len() as u64, rest.len() as u64))
}

/// Validates UTF-8 and borrows a byte-counted protocol payload.
/// The returned byte slice may begin inside a multi-byte character.
pub fn text_payload_bytes(input: &[u8], header: u8) -> Result<Option<&[u8]>, u8> {
    match core::str::from_utf8(input) {
        Ok(text) => Ok(experiment_core::protocol::text_bytes(text).get(header as usize..)),
        Err(_) => Err(4),
    }
}

/// Reports a validated payload's byte length without allocating the payload.
pub fn text_payload_length(input: &[u8], header: u8) -> Result<Option<u64>, u8> {
    match text_payload_bytes(input, header) {
        Ok(payload) => Ok(payload.map(|rest| rest.len() as u64)),
        Err(error) => Err(error),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn split_lengths_account_for_the_entire_input() {
        let input = [0, 255, 128, 65];
        assert_eq!(super::split_lengths(&input, 0), Some((0, 4)));
        assert_eq!(super::split_lengths(&input, 2), Some((2, 2)));
        assert_eq!(super::split_lengths(&input, 4), Some((4, 0)));
        assert_eq!(super::split_lengths(&input, 5), None);
    }
}
