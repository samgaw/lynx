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

/// Appends one record at the current visible end and synchronizes its bytes.
///
/// Callers must serialize appenders and start from a complete record prefix.
/// A short write is not acknowledged and must be recovered before another append.
///
/// # Errors
/// Propagates seek, write and synchronization errors.
pub fn append_record(file: &mut File, value: u16) -> io::Result<bool> {
    match io_core::seek_from(file, std::io::SeekFrom::End(0)) {
        Err(error) => Err(error),
        Ok(_) => write_record(file, value),
    }
}

/// Recovers the valid leading records, stopping on incomplete or invalid input.
///
/// The record limit is explicit: reaching it returns the recovered prefix without
/// inspecting later records. File errors propagate rather than becoming EOF.
///
/// # Errors
/// Propagates seek and read errors.
pub fn recover_log(file: &mut File, max_records: usize) -> io::Result<Vec<u16>> {
    match io_core::seek_to(file, 0) {
        Err(error) => Err(error),
        Ok(_) => {
            let mut values = Vec::new();
            while values.len() < max_records {
                match read_record(file) {
                    Err(error) => return Err(error),
                    Ok(None) => return Ok(values),
                    Ok(Some(value)) => values.push(value),
                }
            }
            Ok(values)
        }
    }
}

/// Reopens a named log, recovers its bounded prefix and closes the owned file.
///
/// # Errors
/// Propagates opening, seeking and reading errors. Closing does not acknowledge
/// durability or repair an invalid suffix.
pub fn reopen_then_recover(path: &str, max_records: usize) -> io::Result<Vec<u16>> {
    let mut file = open_readwrite(path)?;
    let result = recover_log(&mut file, max_records);
    drop(file);
    result
}

/// Changes file length and acknowledges it only after successful synchronization.
///
/// # Errors
/// Propagates length-change and synchronization errors.
pub fn resize_then_sync(file: &File, length: u64) -> io::Result<()> {
    match io_core::resize_to(file, length) {
        Err(error) => Err(error),
        Ok(()) => io_core::synchronize(file),
    }
}

/// Removes an invalid or incomplete suffix after recovering the complete prefix.
///
/// Reaching the record limit returns `None` without changing the file length:
/// the unexamined suffix may contain valid records. Callers must serialize access.
/// A successful `Some` result acknowledges the repaired length after synchronization.
///
/// # Errors
/// Propagates recovery, length-change and synchronization errors.
pub fn repair_log(file: &mut File, max_records: usize) -> io::Result<Option<Vec<u16>>> {
    match recover_log(file, max_records) {
        Err(error) => Err(error),
        Ok(values) => {
            if values.len() == max_records {
                return Ok(None);
            }
            let valid_bytes = match (values.len() as u64).checked_mul(4) {
                Some(bytes) => bytes,
                None => return Ok(None),
            };
            match resize_then_sync(file, valid_bytes) {
                Err(error) => Err(error),
                Ok(()) => Ok(Some(values)),
            }
        }
    }
}

/// Repairs a shared log while holding its file mutex through synchronization.
///
/// Reaching the record limit returns `None` without acknowledging repair.
///
/// # Errors
/// Propagates read, truncation and synchronization errors.
///
/// # Panics
/// Recursive acquisition may panic or block. Callers must not hold this mutex.
pub fn locked_repair(
    mutex: &std::sync::Mutex<File>,
    max_records: usize,
) -> io::Result<Option<Vec<u16>>> {
    let mut guard = match mutex.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    repair_log(&mut guard, max_records)
}

/// Appends under a single native file mutex, retaining IO effects on release.
///
/// # Errors
/// Propagates seek, write and synchronization errors.
///
/// # Panics
/// Recursive acquisition may panic or block. Callers must not hold this mutex.
pub fn locked_append(mutex: &std::sync::Mutex<File>, value: u16) -> io::Result<bool> {
    let mut guard = match mutex.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    append_record(&mut guard, value)
}

/// Appends a complete record or durably removes its short-write tail.
///
/// `Ok(false)` means a short write was truncated back to the original end and
/// that truncation was synchronized. The offset may remain beyond the new end.
/// Callers must serialize access and start from a complete record prefix.
///
/// # Errors
/// Propagates seek, write, length-change and synchronization errors. An error
/// does not promise rollback: callers must recover before a subsequent append.
pub fn append_record_or_rollback(file: &mut File, value: u16) -> io::Result<bool> {
    match io_core::seek_from(file, std::io::SeekFrom::End(0)) {
        Err(error) => Err(error),
        Ok(start) => {
            let bytes = io_core::encode_record(value);
            match io_core::write_once(file, &bytes) {
                Err(error) => Err(error),
                Ok(4) => match io_core::synchronize(file) {
                    Err(error) => Err(error),
                    Ok(()) => Ok(true),
                },
                Ok(_) => match resize_then_sync(file, start) {
                    Err(error) => Err(error),
                    Ok(()) => Ok(false),
                },
            }
        }
    }
}

/// Holds the shared file mutex through append and any required rollback.
///
/// # Errors
/// Propagates the append or rollback error without releasing stale file state.
///
/// # Panics
/// Recursive acquisition may panic or block. Callers must not hold this mutex.
pub fn locked_append_or_rollback(mutex: &std::sync::Mutex<File>, value: u16) -> io::Result<bool> {
    let mut guard = match mutex.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    append_record_or_rollback(&mut guard, value)
}

/// Repairs an existing log before attempting a synchronized append.
///
/// `Ok(false)` does not acknowledge an append: either recovery reached its
/// record limit or a short write was durably rolled back. Callers must serialize
/// the complete repair/append sequence, not only its individual operations.
///
/// # Errors
/// Propagates repair and append errors; a failure can leave an unsynchronized
/// tail which a subsequent call must repair before appending.
pub fn repair_and_append(file: &mut File, max_records: usize, value: u16) -> io::Result<bool> {
    match repair_log(file, max_records)? {
        Some(_records) => append_record_or_rollback(file, value),
        None => Ok(false),
    }
}

/// Holds one file mutex guard through repair, append and synchronization.
///
/// # Errors
/// Propagates repair and append errors without releasing a stale file snapshot.
///
/// # Panics
/// Recursive acquisition may panic or block. Callers must not hold this mutex.
pub fn locked_repair_and_append(
    mutex: &std::sync::Mutex<File>,
    max_records: usize,
    value: u16,
) -> io::Result<bool> {
    let mut guard = match mutex.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    repair_and_append(&mut guard, max_records, value)
}

/// Consumes an owned file. Native close errors are ignored by Rust's destructor.
pub fn consume_file(file: File) {
    drop(file);
}

/// Scope exit invokes the compiler-generated file destructor.
pub fn implicit_close(_file: File) {}

/// Preserves the synchronization result and closes on both result branches.
///
/// # Errors
/// Propagates synchronization errors. Closing does not acknowledge durability.
pub fn synchronize_then_close(file: File) -> io::Result<()> {
    let reply = io_core::synchronize(&file);
    drop(file);
    reply
}

/// Transfers the complete file owner to the first-party cleanup implementation.
pub fn consume_file_mutex(mutex: std::sync::Mutex<File>) {
    io_core::consume_file_mutex(mutex);
}

/// Scope exit destroys both the mutex and its owned file.
pub fn implicit_file_mutex(_mutex: std::sync::Mutex<File>) {}

/// Creates an owned mutex and transfers it across the crate boundary for cleanup.
pub fn file_mutex_cycle(file: File) {
    let mutex = std::sync::Mutex::new(file);
    consume_file_mutex(mutex);
}

/// Opens a read-only handle through a first-party dependency.
/// # Errors
/// Propagates the opening error without creating an owned handle.
pub fn open_readonly(path: &str) -> io::Result<File> {
    io_core::open_readonly(path)
}

/// Opens two independent handles of the same named file.
/// # Errors
/// Propagates either opening error, closing the first handle if the second fails.
pub fn open_pair(path: &str) -> io::Result<(File, File)> {
    let first = io_core::open_readonly(path)?;
    match io_core::open_readonly(path) {
        Ok(second) => Ok((first, second)),
        Err(error) => {
            drop(first);
            Err(error)
        }
    }
}

/// Forwards exclusive creation across the workspace boundary.
/// # Errors
/// Propagates the operating system's exclusive-creation error.
pub fn create_fresh(path: &str) -> io::Result<File> {
    io_core::create_new_file(path)
}

/// Reopens an existing log while retaining read and write access to its inode.
///
/// # Errors
/// Propagates opening errors without replacing or truncating the named file.
pub fn open_readwrite(path: &str) -> io::Result<File> {
    io_core::open_readwrite(path)
}

/// Reopens, durably appends and closes an existing log without replacing it.
///
/// Callers must serialize access and start from a complete record prefix.
///
/// # Errors
/// Propagates opening and append errors; an error does not promise rollback.
pub fn reopen_then_append(path: &str, value: u16) -> io::Result<bool> {
    let mut file = io_core::open_readwrite(path)?;
    let result = append_record_or_rollback(&mut file, value);
    drop(file);
    result
}

/// Renames a regular-file name through the low-level crate.
/// # Errors
/// Propagates the operating system's rename error.
pub fn rename_visible(from: &str, to: &str) -> io::Result<()> {
    io_core::rename_file(from, to)
}

/// Synchronizes the containing directory through a first-party dependency.
/// # Errors
/// Propagates the operating system's opening or synchronization error.
pub fn sync_directory() -> io::Result<()> {
    let directory = io_core::open_readonly(".")?;
    io_core::synchronize(&directory)
}

/// Opens and closes the directory without promising namespace persistence.
/// # Errors
/// Propagates the operating system's opening error.
pub fn close_directory() -> io::Result<()> {
    let _directory = io_core::open_readonly(".")?;
    Ok(())
}

/// Publishes an already-written file only after its data and directory are synced.
/// # Errors
/// Propagates synchronization, rename and directory-opening errors. An error
/// does not promise that the rename was rolled back.
pub fn publish_file(file: File, source: &str, target: &str) -> io::Result<()> {
    synchronize_then_close(file)?;
    io_core::rename_file(source, target)?;
    sync_directory()
}

/// Parses the leading word and closes the owned file on success or I/O error.
/// # Errors
/// Propagates read errors; incomplete input returns no word.
pub fn read_and_close_word(mut file: File) -> io::Result<Option<u16>> {
    let reply = read_word(&mut file);
    drop(file);
    reply
}

/// Reopens a named published file, parses its leading word and closes the handle.
/// # Errors
/// Propagates opening and read errors; incomplete input returns no word.
pub fn recover_named_word(path: &str) -> io::Result<Option<u16>> {
    let file = io_core::open_readonly(path)?;
    read_and_close_word(file)
}

/// Exclusively creates, writes and publishes a word in the admitted directory.
/// A short write closes the temporary file and returns false without publishing.
/// # Errors
/// Propagates creation, write and publication errors. Unacknowledged temporary
/// names may remain; an error does not promise rollback of filesystem effects.
pub fn commit_word(source: &str, target: &str, value: u16) -> io::Result<bool> {
    let mut file = io_core::create_new_file(source)?;
    let written = io_core::write_once(&mut file, &value.to_le_bytes());
    match written {
        Err(error) => {
            drop(file);
            Err(error)
        }
        Ok(2) => {
            publish_file(file, source, target)?;
            Ok(true)
        }
        Ok(_) => {
            drop(file);
            Ok(false)
        }
    }
}

/// Report publication success after consuming any returned I/O error.
///
/// # Panics
/// A custom I/O error payload's destructor may panic. The verification model
/// admits only registered callback-free operating-system errors.
pub fn commit_ack(value: u16) -> bool {
    match commit_word("a", "b", value) {
        Ok(complete) => complete,
        Err(error) => {
            io_core::discard_io_error(error);
            false
        }
    }
}

/// Acknowledges handling an admitted OS error after its first-party destructor call.
///
/// Verification admits only registered callback-free operating-system errors.
///
/// # Panics
/// A custom error payload's destructor may panic.
pub fn discard_error_ack(error: io::Error) -> bool {
    io_core::discard_io_error(error);
    true
}

/// Write once before applying request policy and consuming the file.
///
/// # Errors
/// Returns one for an operating-system write error.
///
/// # Panics
/// Rejection panics after the write; scope destruction closes the file.
pub fn checked_write(mut file: File, bytes: &[u8], accepted: bool) -> Result<usize, u8> {
    let result = match io_core::write_once(&mut file, bytes) {
        Ok(written) => Ok(written),
        Err(error) => {
            drop(error);
            Err(1)
        }
    };
    io_core::require_write(accepted);
    result
}

/// Applies request policy while owning an admitted operating-system error.
///
/// # Panics
/// Rejection destroys the owned error while unwinding.
pub fn checked_error(error: io::Error, accepted: bool) {
    io_core::require_write(accepted);
    drop(error);
}

/// Applies request policy while owning a file through a mutex.
///
/// # Panics
/// Rejection closes the file and disposes the mutex while unwinding.
pub fn checked_file_mutex(file: File, accepted: bool) {
    let mutex = std::sync::Mutex::new(file);
    io_core::require_write(accepted);
    drop(mutex);
}

/// Retains an owned file and a completed write across a cross-crate suspension.
///
/// # Errors
/// Returns one for an operating-system write error, consuming its payload.
/// Cancellation closes the file without undoing the completed write or syncing it.
pub async fn suspended_write(mut file: File, bytes: [u8; 2]) -> Result<usize, u8> {
    let reply = match io_core::write_once(&mut file, &bytes) {
        Ok(written) => Ok(written),
        Err(error) => {
            drop(error);
            Err(1)
        }
    };
    io_core::yield_once().await;
    drop(file);
    reply
}

/// Polls the actual writer once, optionally resuming it, then consumes its frame.
///
/// Returns None for cancellation while Pending. Uses the standard no-op waker;
/// this bounded caller does not claim to implement a general async executor.
/// A returned write error is represented by one.
pub fn poll_write(file: File, bytes: [u8; 2], resume: bool) -> Option<Result<usize, u8>> {
    use std::future::Future;
    use std::task::{Context, Poll, Waker};
    let mut context = Context::from_waker(Waker::noop());
    let mut writer = std::pin::pin!(suspended_write(file, bytes));
    match writer.as_mut().poll(&mut context) {
        Poll::Ready(reply) => Some(reply),
        Poll::Pending => {
            if resume {
                match writer.as_mut().poll(&mut context) {
                    Poll::Ready(reply) => Some(reply),
                    Poll::Pending => None,
                }
            } else {
                None
            }
        }
    }
}

/// Writes under a shared file lock, retaining the guard across suspension.
///
/// # Errors
/// Returns one on write failure after consuming the OS error payload. Poisoned
/// locks are recovered without clearing their poison flag.
///
/// # Panics
/// Recursive acquisition may block or panic; the verification model rejects it.
#[expect(
    clippy::await_holding_lock,
    reason = "Verification fixture retains a lease across Pending"
)]
pub async fn locked_suspended_write(
    mutex: &std::sync::Mutex<File>,
    bytes: [u8; 2],
) -> Result<usize, u8> {
    let mut guard = match mutex.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let reply = match io_core::write_once(&mut guard, &bytes) {
        Ok(written) => Ok(written),
        Err(error) => {
            drop(error);
            Err(1)
        }
    };
    io_core::yield_once().await;
    drop(guard);
    reply
}

/// Polls once, optionally resumes, then destroys the retained guarded frame.
///
/// Cancellation retains completed writes and releases the guard. It does not
/// close the file, synchronize storage, or roll back writes.
///
/// # Panics
/// Recursive acquisition may block or panic; the verification model rejects it.
pub fn poll_locked_write(
    mutex: &std::sync::Mutex<File>,
    bytes: [u8; 2],
    resume: bool,
) -> Option<Result<usize, u8>> {
    use std::future::Future;
    use std::task::{Context, Poll, Waker};
    let mut context = Context::from_waker(Waker::noop());
    let mut writer = std::pin::pin!(locked_suspended_write(mutex, bytes));
    match writer.as_mut().poll(&mut context) {
        Poll::Ready(reply) => Some(reply),
        Poll::Pending => {
            if resume {
                match writer.as_mut().poll(&mut context) {
                    Poll::Ready(reply) => Some(reply),
                    Poll::Pending => None,
                }
            } else {
                None
            }
        }
    }
}

/// Reads one little-endian word at an absolute offset under the shared file lock.
///
/// # Errors
/// Returns one for seeking or reading failure, consuming the OS error payload.
/// The guard is released after success, EOF and either I/O failure.
///
/// # Panics
/// Recursive acquisition may block or panic; the verification model rejects it.
pub fn locked_word(mutex: &std::sync::Mutex<File>, offset: u64) -> Result<Option<u16>, u8> {
    let mut guard = match mutex.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let reply = match io_core::seek_from(&mut guard, std::io::SeekFrom::Start(offset)) {
        Ok(_) => match read_word(&mut guard) {
            Ok(value) => Ok(value),
            Err(error) => {
                drop(error);
                Err(1)
            }
        },
        Err(error) => {
            drop(error);
            Err(1)
        }
    };
    drop(guard);
    reply
}

/// Writes before suspension and synchronizes the accepted prefix on resumption.
///
/// Cancellation releases the guard without synchronizing or rolling back writes.
/// A returned count acknowledges only that prefix, including short writes.
///
/// # Errors
/// Returns one for a write failure and two for a synchronization failure, after
/// consuming the OS error. Poisoned locks are recovered without clearing poison.
///
/// # Panics
/// Recursive acquisition may block or panic; the verification model rejects it.
#[expect(
    clippy::await_holding_lock,
    reason = "Verification fixture retains a lease until synchronization or cancellation"
)]
pub async fn locked_suspended_sync(
    mutex: &std::sync::Mutex<File>,
    bytes: [u8; 2],
) -> Result<usize, u8> {
    let mut guard = match mutex.lock() {
        Ok(guard) => guard,
        Err(error) => error.into_inner(),
    };
    let written = match io_core::write_once(&mut guard, &bytes) {
        Ok(count) => Ok(count),
        Err(error) => {
            drop(error);
            Err(1)
        }
    };
    io_core::yield_once().await;
    let reply = synchronize_written(&guard, written);
    drop(guard);
    reply
}

/// Polls the guarded synchronization future once or resumes it once.
///
/// Dropping the pending future cancels synchronization and retains the write.
///
/// # Panics
/// Recursive acquisition may block or panic; the verification model rejects it.
pub fn poll_locked_sync(
    mutex: &std::sync::Mutex<File>,
    bytes: [u8; 2],
    resume: bool,
) -> Option<Result<usize, u8>> {
    use std::future::Future;
    use std::task::{Context, Poll, Waker};
    let mut context = Context::from_waker(Waker::noop());
    let mut writer = std::pin::pin!(locked_suspended_sync(mutex, bytes));
    match writer.as_mut().poll(&mut context) {
        Poll::Ready(reply) => Some(reply),
        Poll::Pending => {
            if resume {
                match writer.as_mut().poll(&mut context) {
                    Poll::Ready(reply) => Some(reply),
                    Poll::Pending => None,
                }
            } else {
                None
            }
        }
    }
}

/// Synchronizes a successful write, preserving its actual count or write error.
///
/// # Errors
/// Preserves write errors and returns two for synchronization failure.
fn synchronize_written(file: &File, written: Result<usize, u8>) -> Result<usize, u8> {
    match written {
        Ok(count) => match io_core::synchronize(file) {
            Ok(()) => Ok(count),
            Err(error) => {
                drop(error);
                Err(2)
            }
        },
        Err(error) => Err(error),
    }
}

/// Reopens two words using fresh file and lock state after a restart.
///
/// Truncated words return `None`; no old resource or mutex capability is reused.
///
/// # Errors
/// Returns three for opening failure and one for seeking or reading failure.
pub fn reopen_words(path: &str) -> Result<(Option<u16>, Option<u16>), u8> {
    let file = match io_core::open_readonly(path) {
        Ok(file) => file,
        Err(error) => {
            drop(error);
            return Err(3);
        }
    };
    let mutex = std::sync::Mutex::new(file);
    let reply = match locked_word(&mutex, 0) {
        Err(error) => Err(error),
        Ok(first) => match locked_word(&mutex, 2) {
            Err(error) => Err(error),
            Ok(second) => Ok((first, second)),
        },
    };
    drop(mutex);
    reply
}

/// Propagates standard truncation classification across a workspace dependency.
pub fn truncated_input(kind: io::ErrorKind) -> bool {
    io_core::is_truncated(kind)
}

/// Recognizes an interrupted operation by classifying its actual borrowed error.
pub fn error_is_retryable(error: &io::Error) -> bool {
    io_core::is_retryable(io_core::error_kind(error))
}

/// Attempts one read and reports whether an error permits retrying.
///
/// The returned error and opened file are consumed on their actual control paths.
pub fn read_is_retryable(path: &str) -> bool {
    let mut file = match io_core::open_readonly(path) {
        Ok(file) => file,
        Err(error) => {
            let retryable = error_is_retryable(&error);
            drop(error);
            return retryable;
        }
    };
    let mut byte = [0u8];
    let retryable = match io_core::read_once(&mut file, &mut byte) {
        Ok(_) => false,
        Err(error) => {
            let retryable = error_is_retryable(&error);
            drop(error);
            retryable
        }
    };
    drop(file);
    retryable
}

/// Reads an optional word while distinguishing truncation from other IO errors.
///
/// # Errors
/// Returns errors other than unexpected EOF from the actual workspace reader.
pub fn optional_exact_word(file: &mut File) -> io::Result<Option<u16>> {
    match io_core::exact_word(file) {
        Ok(value) => Ok(Some(value)),
        Err(error) if error.kind() == io::ErrorKind::UnexpectedEof => Ok(None),
        Err(error) => Err(error),
    }
}

/// Opens a protocol input and reads one optional little-endian word.
///
/// # Errors
/// Returns two for opening failure and one for a non-EOF reading failure.
pub fn read_exact_optional(path: &str) -> Result<Option<u16>, u8> {
    let mut file = match io_core::open_readonly(path) {
        Ok(file) => file,
        Err(error) => {
            drop(error);
            return Err(2);
        }
    };
    let reply = match optional_exact_word(&mut file) {
        Ok(value) => Ok(value),
        Err(error) => {
            drop(error);
            Err(1)
        }
    };
    drop(file);
    reply
}

/// Decodes a word and reports exact remaining input length across the crate boundary.
/// # Errors
/// Propagates the actual standard slice-reader error.
pub fn parse_slice(input: &mut &[u8]) -> io::Result<(u16, usize)> {
    let value = io_core::slice_word(input)?;
    Ok((value, input.len()))
}

/// Decodes a binary word and exposes the exact unconsumed length.
/// # Errors
/// Returns one when the standard slice reader reports truncation.
pub fn parse_packet(input: &[u8]) -> Result<(u16, u64), u8> {
    let mut remaining = input;
    match parse_slice(&mut remaining) {
        Ok((value, count)) => Ok((value, count as u64)),
        Err(error) => {
            drop(error);
            Err(1)
        }
    }
}

#[cfg(unix)]
pub mod positional;
