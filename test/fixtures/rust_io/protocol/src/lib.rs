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

/// Recovers the leading word regardless of the incoming file position.
///
/// # Errors
/// Propagates seek and read errors; incomplete input returns no word.
pub fn recover_word(file: &mut File) -> io::Result<Option<u16>> {
    match io_core::seek_to(file, 0) {
        Err(error) => Err(error),
        Ok(_) => read_word(file),
    }
}

/// Acknowledges a fresh four-byte record only after all bytes are synchronized.
///
/// # Errors
/// Propagates write and synchronization errors. A short write is not acknowledged.
pub fn write_record(file: &mut File, value: u16) -> io::Result<bool> {
    let encoded = io_core::encode_record(value);
    match write_then_sync(file, &encoded) {
        Err(error) => Err(error),
        Ok(4) => Ok(true),
        Ok(_) => Ok(false),
    }
}

/// Reads a fresh record, rejecting truncation and a failed complement check.
///
/// # Errors
/// Propagates read errors without returning an accepted record.
pub fn read_record(file: &mut File) -> io::Result<Option<u16>> {
    match read_word(file) {
        Err(error) => Err(error),
        Ok(None) => Ok(None),
        Ok(Some(value)) => match read_word(file) {
            Err(error) => Err(error),
            Ok(None) => Ok(None),
            Ok(Some(inverse)) => Ok(io_core::decode_record(value, inverse)),
        },
    }
}

/// Recovers the first fresh record regardless of the incoming file position.
///
/// # Errors
/// Propagates seek and read errors. Incomplete or invalid records return no value.
pub fn recover_record(file: &mut File) -> io::Result<Option<u16>> {
    match io_core::seek_to(file, 0) {
        Err(error) => Err(error),
        Ok(_) => read_record(file),
    }
}
