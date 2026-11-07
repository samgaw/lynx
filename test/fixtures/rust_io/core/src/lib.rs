//! Individual regular-file operations; OS behavior is an explicit model boundary.
use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom, Write};

/// Writes once, retaining partial-write and error results.
///
/// # Errors
/// Returns the operating system's write error.
pub fn write_once(file: &mut File, bytes: &[u8]) -> io::Result<usize> {
    file.write(bytes)
}

/// Synchronizes file contents separately from write completion.
///
/// # Errors
/// Returns the operating system's synchronization error.
pub fn synchronize(file: &File) -> io::Result<()> {
    file.sync_all()
}

/// Reads once, retaining partial-read, EOF and error results.
///
/// # Errors
/// Returns the operating system's read error.
pub fn read_once(file: &mut File, bytes: &mut [u8]) -> io::Result<usize> {
    file.read(bytes)
}

/// Positions a borrowed file at an absolute byte offset.
///
/// # Errors
/// Returns the operating system's seek error.
pub fn seek_to(file: &mut File, offset: u64) -> io::Result<u64> {
    seek_from(file, SeekFrom::Start(offset))
}

/// Seeks from the start, current offset or end with the actual standard enum.
///
/// # Errors
/// Returns the operating system's seek error.
pub fn seek_from(file: &mut File, origin: SeekFrom) -> io::Result<u64> {
    file.seek(origin)
}

/// Encodes a word followed by its complement for a fresh record slot.
pub fn encode_record(value: u16) -> [u8; 4] {
    let [low, high] = value.to_le_bytes();
    let [inverse_low, inverse_high] = (!value).to_le_bytes();
    [low, high, inverse_low, inverse_high]
}

/// Accepts a record only when both words are exact complements.
pub fn decode_record(value: u16, inverse: u16) -> Option<u16> {
    if value ^ inverse == u16::MAX {
        Some(value)
    } else {
        None
    }
}

/// Sets the visible file length without acknowledging persistence.
///
/// # Errors
/// Returns the operating system's length-change error.
pub fn resize_to(file: &File, length: u64) -> io::Result<()> {
    file.set_len(length)
}

/// Consumes the mutex and its owned file, including when poisoned.
pub fn consume_file_mutex(mutex: std::sync::Mutex<File>) {
    drop(mutex);
}
