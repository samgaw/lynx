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
