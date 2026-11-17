//! Byte-range updates and observations through a shared descriptor.
use std::{fs::File, io};

/// Acknowledges only the prefix accepted by the positional write.
///
/// # Errors
/// Propagates write and data synchronization errors.
pub fn patch(file: &File, offset: u64, bytes: &[u8]) -> io::Result<usize> {
    let written = io_core::positional::write_at(file, bytes, offset)?;
    file.sync_data()?;
    Ok(written)
}

/// Reads a byte range without consuming the descriptor's sequential cursor.
///
/// # Errors
/// Propagates the operating system's read error.
pub fn observe(file: &File, offset: u64, buffer: &mut [u8]) -> io::Result<usize> {
    io_core::positional::read_at(file, buffer, offset)
}
