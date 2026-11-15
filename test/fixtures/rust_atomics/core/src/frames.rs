//! Incremental framing over owned input. Incomplete or invalid frames keep input.

/// Splits owned bytes using the standard Vec operation.
///
/// # Panics
/// Panics when the requested position exceeds the input length.
pub fn split_buffer(input: &mut Vec<u8>, position: usize) -> Vec<u8> {
    input.split_off(position)
}

/// Takes one version-one frame with a two-byte network-order payload length.
/// Returned frames include their three-byte header; trailing bytes stay in input.
/// An incomplete header/payload returns None and a wrong version returns error 1.
///
/// # Panics
/// May panic on allocation failure according to the configured allocator policy.
pub fn take_frame(input: &mut Vec<u8>) -> Result<Option<Vec<u8>>, u8> {
    if input.len() < 3 {
        return Ok(None);
    }
    if input[0] != 1 {
        return Err(1);
    }
    let length = u16::from_be_bytes([input[1], input[2]]) as usize;
    let end = 3 + length;
    if input.len() < end {
        return Ok(None);
    }
    let suffix = split_buffer(input, end);
    let frame = std::mem::replace(input, suffix);
    Ok(Some(frame))
}

#[cfg(test)]
mod tests {
    use super::{split_buffer, take_frame};

    #[test]
    fn consumes_one_frame_and_retains_the_next() {
        let mut input = vec![1, 0, 2, 128, 255, 1, 0, 0];
        assert_eq!(take_frame(&mut input), Ok(Some(vec![1, 0, 2, 128, 255])));
        assert_eq!(input, vec![1, 0, 0]);
        assert_eq!(take_frame(&mut input), Ok(Some(vec![1, 0, 0])));
        assert!(input.is_empty());
    }

    #[test]
    fn incomplete_and_invalid_frames_do_not_consume_input() {
        for bytes in [vec![], vec![1, 0], vec![1, 0, 2, 42], vec![2, 0, 0]] {
            let mut input = bytes.clone();
            let result = take_frame(&mut input);
            assert!(matches!(result, Ok(None) | Err(1)));
            assert_eq!(input, bytes);
        }
    }

    #[test]
    #[should_panic(expected = "split index")]
    fn out_of_range_split_panics() {
        split_buffer(&mut vec![1], 2);
    }
}
