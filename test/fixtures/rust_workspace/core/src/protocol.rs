//! A small binary protocol and standalone parsing operations.

/// Compares a borrowed prefix using the actual element comparator.
pub fn has_prefix<T: PartialEq>(input: &[T], prefix: &[T]) -> bool {
    input.starts_with(prefix)
}

/// Consumes a borrowed prefix using Rust's pattern conversion and comparison order.
pub fn consume_prefix<'a, T: PartialEq>(input: &'a [T], prefix: &[T]) -> Option<&'a [T]> {
    input.strip_prefix(prefix)
}

/// Consumes the array marker without an implicit conversion at the call site.
pub fn consume_array_marker(input: &[u8]) -> Option<&[u8]> {
    input.strip_prefix(b"LYNX")
}

/// Demonstrates that prefix consumption compares the input before the pattern.
///
/// # Panics
/// Panics when the input's reserved token is compared with the pattern.
pub fn checked_consume() -> bool {
    let input = [CheckedByte(255)];
    let prefix = [CheckedByte(1)];
    match input.strip_prefix(&prefix) {
        Some(payload) => payload.is_empty(),
        None => false,
    }
}

/// The same operands short-circuit without a panic in starts_with's order.
pub fn checked_recognize() -> bool {
    let input = [CheckedByte(255)];
    let prefix = [CheckedByte(1)];
    input.starts_with(&prefix)
}

/// A protocol token whose comparison may reject the reserved byte.
#[derive(Debug)]
pub struct CheckedByte(pub u8);

impl PartialEq for CheckedByte {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    #[expect(
        clippy::partialeq_ne_impl,
        reason = "exercises retained custom inequality dispatch and panic ordering"
    )]
    fn ne(&self, other: &Self) -> bool {
        assert!(self.0 != 255, "reserved protocol token");
        self.0 != other.0
    }
}

/// Checks short-circuit comparison before a reserved token can panic.
///
/// # Panics
/// Panics at the second token when the first tokens match.
pub fn checked_prefix(matches: bool) -> bool {
    let input = [CheckedByte(2), CheckedByte(255)];
    let prefix = [CheckedByte(if matches { 2 } else { 1 }), CheckedByte(255)];
    has_prefix(&input, &prefix)
}

/// Borrows a length-delimited prefix, rejecting truncated input without panicking.
pub fn prefix(input: &[u8], length: u8) -> Option<&[u8]> {
    input.get(..length as usize)
}

/// Borrows a window, rejecting reversed or out-of-bounds endpoints.
pub fn window(input: &[u8], start: usize, end: usize) -> Option<&[u8]> {
    input.get(start..end)
}

/// Borrows the bytes remaining after a validated position.
pub fn remainder(input: &[u8], start: usize) -> Option<&[u8]> {
    input.get(start..)
}

/// Borrows a window, preserving Rust's panic on invalid endpoints.
pub fn indexed_window(input: &[u8], start: usize, end: usize) -> &[u8] {
    &input[start..end]
}

/// Borrows a prefix, preserving Rust's bounds panic.
pub fn indexed_prefix(input: &[u8], end: usize) -> &[u8] {
    &input[..end]
}

/// Borrows the remainder, preserving Rust's bounds panic.
pub fn indexed_remainder(input: &[u8], start: usize) -> &[u8] {
    &input[start..]
}

/// Counts a window in a fixed protocol buffer using array-to-slice delegation.
pub fn array_window_length(start: usize, end: usize) -> u64 {
    let bytes = [0_u8, 255, 128];
    bytes[start..end].len() as u64
}

/// Exercises the unqualified RangeFrom failure model through an array wrapper.
pub fn indexed_array_remainder(input: &[u8; 3], start: usize) -> usize {
    input[start..].len()
}

/// Exercises the unqualified RangeFrom model through vector delegation.
pub fn indexed_vector_remainder(input: Vec<u8>, start: usize) -> usize {
    input[start..].len()
}

/// Parses a bounded frame: version byte, payload byte count, then UTF-8 bytes.
/// Error codes distinguish short headers, versions, lengths and invalid text.
pub fn parse_frame(input: &[u8]) -> Result<u64, u8> {
    if input.len() < 2 {
        return Err(1);
    }
    if input[0] != 1 {
        return Err(2);
    }
    let length = input[1] as usize;
    if input.len() != length + 2 {
        return Err(3);
    }
    let (_, payload) = input.split_at(2);
    match core::str::from_utf8(payload) {
        Ok(_) => Ok(length as u64),
        Err(_) => Err(4),
    }
}

/// Exposes exact UTF-8 error positions; zero length denotes truncation.
pub fn utf8_status(input: &[u8]) -> Result<u64, (u64, u8)> {
    match core::str::from_utf8(input) {
        Ok(_) => Ok(input.len() as u64),
        Err(error) => Err((
            error.valid_up_to() as u64,
            match error.error_len() {
                Some(length) => length as u8,
                None => 0,
            },
        )),
    }
}

/// Borrows the original UTF-8 bytes without allocation.
pub fn text_bytes(text: &str) -> &[u8] {
    text.as_bytes()
}

/// Counts bytes rather than Unicode scalar values.
pub fn text_length(text: &str) -> usize {
    text.len()
}

/// Tests whether a borrowed string has no bytes.
pub fn text_empty(text: &str) -> bool {
    text.is_empty()
}

/// Provides an immutable empty default without allocating a buffer.
pub fn default_bytes() -> &'static [u8] {
    &[]
}

/// Provides the fixed wire-format marker from its actual promoted initializer.
pub fn magic_bytes() -> &'static [u8] {
    &[76, 89, 78, 88]
}

/// Fixed wire-format marker shared by protocol operations.
pub const WIRE_MAGIC: [u8; 4] = [76, 89, 78, 88];

/// Interprets the shared marker in network byte order.
pub fn named_magic_word() -> u32 {
    u32::from_be_bytes(WIRE_MAGIC)
}

/// Shared borrowed wire marker in the form used by protocol parsers.
pub const BORROWED_MAGIC: &[u8] = b"LYNX";

/// Binary tag bytes have no UTF-8 requirement.
pub const BINARY_TAG: &[u8] = b"L\0\xff";

/// Borrows the exact named marker bytes.
pub fn borrowed_magic_bytes() -> &'static [u8] {
    BORROWED_MAGIC
}

/// Parses the named marker through the ordinary checked header reader.
pub fn borrowed_magic_word() -> Option<u32> {
    read_header(borrowed_magic_bytes())
}

/// Borrows the exact named binary tag, including zero and non-UTF-8 bytes.
pub fn binary_tag_bytes() -> &'static [u8] {
    BINARY_TAG
}

/// Exercises the bounds-checked indexing primitive independently of NIFs.
///
/// # Panics
/// Panics when the input is empty.
pub fn first(input: &[u8]) -> u8 {
    input[0]
}

/// Exercises a shared slice split independently of NIFs.
///
/// # Panics
/// Panics when the split position exceeds the input length.
pub fn prefix_length(input: &[u8], position: usize) -> usize {
    input.split_at(position).0.len()
}

/// Roundtrips a fixed-width protocol integer in little-endian order.
pub fn little_endian_roundtrip(value: u32) -> u32 {
    u32::from_le_bytes(value.to_le_bytes())
}

/// Roundtrips a fixed-width protocol integer in big-endian order.
pub fn big_endian_roundtrip(value: u32) -> u32 {
    u32::from_be_bytes(value.to_be_bytes())
}

/// Reads a four-byte big-endian header, rejecting short input before indexing.
pub fn read_header(input: &[u8]) -> Option<u32> {
    if input.len() < 4 {
        return None;
    }
    Some(u32::from_be_bytes([input[0], input[1], input[2], input[3]]))
}

#[cfg(test)]
mod tests {
    use super::{
        big_endian_roundtrip, little_endian_roundtrip, parse_frame, read_header, utf8_status,
    };

    #[test]
    fn custom_comparison_preserves_short_circuit_and_panic() {
        assert!(!super::checked_prefix(false));
        assert!(std::panic::catch_unwind(|| super::checked_prefix(true)).is_err());
        assert!(super::has_prefix(&[0_u8, 255, 128], &[0, 255]));
        assert!(!super::has_prefix(&[0_u8], &[0, 255]));
        assert!(!super::checked_recognize());
        assert!(std::panic::catch_unwind(super::checked_consume).is_err());
        assert_eq!(
            super::consume_prefix(&[0_u8, 255, 128], &[0, 255]),
            Some(&[128][..])
        );
        assert_eq!(
            super::consume_array_marker(b"LYNX\0\xff"),
            Some(&[0, 255][..])
        );
    }

    #[test]
    fn borrowed_prefix_bounds_and_contents() {
        let input = [0, 255, 128, 65];
        assert_eq!(super::prefix(&input, 2), Some(&[0, 255][..]));
        assert_eq!(super::prefix(&input, 4), Some(&input[..]));
        assert_eq!(super::prefix(&input, 5), None);
        assert_eq!(super::prefix(&input, u8::MAX), None);
        assert_eq!(super::prefix(&[], 0), Some(&[][..]));
        assert_eq!(super::prefix(&[], 1), None);
        assert_eq!(super::window(&input, 1, 3), Some(&[255, 128][..]));
        assert_eq!(super::window(&input, 3, 1), None);
        assert_eq!(super::remainder(&input, 2), Some(&[128, 65][..]));
        assert_eq!(super::remainder(&input, 4), Some(&[][..]));
        assert_eq!(super::remainder(&input, 5), None);
    }

    #[test]
    fn fixed_width_byte_orders_and_header_bounds() {
        for value in [0, 1, 0x1234_5678, u32::MAX] {
            assert_eq!(little_endian_roundtrip(value), value);
            assert_eq!(big_endian_roundtrip(value), value);
        }
        for short in [&[][..], &[1][..], &[1, 2, 3][..]] {
            assert_eq!(read_header(short), None);
        }
        assert_eq!(
            read_header(&[0x12, 0x34, 0x56, 0x78, 0xff]),
            Some(0x1234_5678)
        );
        assert_eq!(read_header(&[0xff; 4]), Some(u32::MAX));
    }

    #[test]
    fn framing_and_utf8_boundaries() {
        for payload in ["", "ascii", "é", "€", "😀", "a\0z"] {
            let mut frame = vec![1, payload.len() as u8];
            frame.extend_from_slice(payload.as_bytes());
            assert_eq!(parse_frame(&frame), Ok(payload.len() as u64));
        }
        for (frame, code) in [
            (&[][..], 1),
            (&[1][..], 1),
            (&[2, 0][..], 2),
            (&[1, 2, 65][..], 3),
            (&[1, 1, 255][..], 4),
        ] {
            assert_eq!(parse_frame(frame), Err(code));
        }
        for (input, offset, length) in [
            (&[255][..], 0, 1),
            (&[65, 194][..], 1, 0),
            (&[224, 128, 128][..], 0, 1),
            (&[237, 160, 128][..], 0, 1),
            (&[240, 144, 128, 65][..], 0, 3),
            (&[244, 144, 128, 128][..], 0, 1),
        ] {
            assert_eq!(utf8_status(input), Err((offset, length)));
        }
    }
}
