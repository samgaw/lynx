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

/// Opens an existing regular file for reading.
/// # Errors
/// Propagates pathname and operating-system errors.
pub fn open_readonly(path: &str) -> io::Result<File> {
    File::open(path)
}

/// Opens an existing log for recovery and subsequent writes without truncation.
///
/// # Errors
/// Propagates pathname, permission and operating-system errors.
pub fn open_readwrite(path: &str) -> io::Result<File> {
    std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(path)
}

/// Creates a fresh readable and writable file without replacing an existing name.
/// # Errors
/// Propagates the operating system's exclusive-creation error.
pub fn create_new_file(path: &str) -> io::Result<File> {
    File::create_new(path)
}

/// Renames a file within the admitted directory.
/// # Errors
/// Propagates the operating system's rename error.
pub fn rename_file(from: &str, to: &str) -> io::Result<()> {
    std::fs::rename(from, to)
}

/// Consume an I/O error after a caller has handled its failure.
///
/// Verification admits registered callback-free operating-system errors and
/// checked allocation-free standard errors. Custom error payloads may execute
/// arbitrary destruction and require separate implementation support.
///
/// # Panics
/// A custom error payload's destructor may panic.
pub fn discard_io_error(error: io::Error) {
    drop(error);
}

/// Consume an I/O error through the compiler-generated scope cleanup.
///
/// Verification has the same admission requirements as [`discard_io_error`].
///
/// # Panics
/// A custom error payload's destructor may panic.
pub fn discard_io_error_implicit(_error: io::Error) {}

/// Reject a request after performing its I/O operation.
///
/// # Panics
/// Panics when the request is rejected.
pub fn require_write(accepted: bool) {
    assert!(accepted);
}

/// A first-party future that suspends and requests one wakeup before completing.
#[derive(Debug)]
pub struct YieldOnce {
    /// Whether the next poll must suspend.
    pub waiting: bool,
}

impl std::future::Future for YieldOnce {
    type Output = ();

    fn poll(
        self: std::pin::Pin<&mut Self>,
        context: &mut std::task::Context<'_>,
    ) -> std::task::Poll<()> {
        let this = self.get_mut();
        if this.waiting {
            this.waiting = false;
            context.waker().wake_by_ref();
            std::task::Poll::Pending
        } else {
            std::task::Poll::Ready(())
        }
    }
}

/// Constructs a future that suspends before returning.
pub fn yield_once() -> YieldOnce {
    YieldOnce { waiting: true }
}

/// Standard error kind produced when a complete protocol input is unavailable.
pub const TRUNCATED_INPUT: io::ErrorKind = io::ErrorKind::UnexpectedEof;

/// Classifies the standard truncation kind using its actual derived comparison.
pub fn is_truncated(kind: io::ErrorKind) -> bool {
    kind == TRUNCATED_INPUT
}

/// Reads the standard classification of a borrowed error without consuming it.
pub fn error_kind(error: &io::Error) -> io::ErrorKind {
    error.kind()
}

/// Recognizes the standard retryable interruption classification.
pub fn is_retryable(kind: io::ErrorKind) -> bool {
    kind == io::ErrorKind::Interrupted
}

/// Fills the caller's buffer through the actual standard exact-read method.
///
/// # Errors
/// Returns the standard error, preserving any earlier reads and buffer changes.
pub fn fill_exact(file: &mut File, buffer: &mut [u8]) -> io::Result<()> {
    file.read_exact(buffer)
}

/// Reads a little-endian protocol word through the workspace reader.
///
/// # Errors
/// Returns the standard exact-read error without replacing its kind.
pub fn exact_word(file: &mut File) -> io::Result<u16> {
    let mut bytes = [0; 2];
    fill_exact(file, &mut bytes)?;
    Ok(u16::from_le_bytes(bytes))
}

/// Fills a destination through the actual standard byte-slice reader.
/// # Errors
/// Short input is consumed and returns the standard UnexpectedEof error.
pub fn fill_slice(input: &mut &[u8], output: &mut [u8]) -> io::Result<()> {
    input.read_exact(output)
}

/// Reads a little-endian word and retains the unread input suffix.
/// # Errors
/// Propagates the standard exact-read error.
pub fn slice_word(input: &mut &[u8]) -> io::Result<u16> {
    let mut bytes = [0; 2];
    fill_slice(input, &mut bytes)?;
    Ok(u16::from_le_bytes(bytes))
}

/// Borrows the suffix beginning at a checked offset.
/// # Panics
/// Panics when the offset exceeds the input length.
pub fn slice_suffix(input: &[u8], start: usize) -> &[u8] {
    &input[start..]
}
