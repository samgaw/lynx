//! Positional I/O leaves the descriptor cursor available for sequential readers.
use std::fs::File;
use std::io;
use std::os::unix::fs::FileExt;

/// Writes the accepted prefix to an explicit byte offset.
///
/// # Errors
/// Propagates the operating system's write error.
pub fn write_at(file: &File, data: &[u8], offset: u64) -> io::Result<usize> {
    file.write_at(data, offset)
}

/// Reads from an explicit byte offset into an initialized buffer.
///
/// # Errors
/// Propagates the operating system's read error.
pub fn read_at(file: &File, data: &mut [u8], offset: u64) -> io::Result<usize> {
    file.read_at(data, offset)
}

/// Fills an initialized buffer from the given offset.
///
/// # Errors
/// Returns unexpected EOF if the buffer cannot be filled, or the first
/// non-interrupted operating system read error.
pub fn read_exact_at(file: &File, buffer: &mut [u8], offset: u64) -> io::Result<()> {
    FileExt::read_exact_at(file, buffer, offset)
}

/// Writes the full slice at the supplied offset, retrying interrupted operations.
///
/// # Errors
/// Propagates the first non-interrupted OS write error, or a zero-byte write.
pub fn write_all_at(file: &File, bytes: &[u8], offset: u64) -> io::Result<()> {
    FileExt::write_all_at(file, bytes, offset)
}
