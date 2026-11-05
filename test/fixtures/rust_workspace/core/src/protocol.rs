//! A small binary protocol and standalone parsing operations.

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

#[cfg(test)]
mod tests {
    use super::{parse_frame, utf8_status};

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
