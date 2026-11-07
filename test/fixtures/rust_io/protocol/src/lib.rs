//! First-party ordering between partial writes and synchronization.
use std::fs::File;
use std::io;

/// Returns the written prefix length only after successful synchronization.
///
/// A short write remains a short write; this does not acknowledge the whole input.
///
/// # Errors
/// Propagates write and synchronization errors without reporting success.
pub fn write_then_sync(file: &mut File, bytes: &[u8]) -> io::Result<usize> {
    match io_core::write_once(file, bytes) {
        Err(error) => Err(error),
        Ok(written) => match io_core::synchronize(file) {
            Err(error) => Err(error),
            Ok(()) => Ok(written),
        },
    }
}

/// Reads a little-endian word, rejecting EOF in either byte.
///
/// # Errors
/// Propagates the first read error without claiming a complete word.
pub fn read_word(file: &mut File) -> io::Result<Option<u16>> {
    let mut first = [0u8];
    match io_core::read_once(file, &mut first) {
        Err(error) => Err(error),
        Ok(0) => Ok(None),
        Ok(_) => {
            let mut second = [0u8];
            match io_core::read_once(file, &mut second) {
                Err(error) => Err(error),
                Ok(0) => Ok(None),
                Ok(_) => {
                    let [low] = first;
                    let [high] = second;
                    Ok(Some(u16::from_le_bytes([low, high])))
                }
            }
        }
    }
}
