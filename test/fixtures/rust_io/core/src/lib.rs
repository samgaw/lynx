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
