//! Individual regular-file operations; OS behavior is an explicit model boundary.
use std::fs::File;
use std::io::{self, Read, Write};

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
