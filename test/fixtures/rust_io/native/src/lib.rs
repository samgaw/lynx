//! Rustler facade for a first-party filesystem publication protocol.

/// Publish a complete word and report whether it was acknowledged.
#[rustler::nif(name = "commit", schedule = "DirtyIo")]
fn commit_nif(value: u16) -> bool {
    io_protocol::commit_ack(value)
}

rustler::init!("Elixir.LynxIoFixture.Native");

#[cfg(feature = "shared-log")]
pub mod shared_log {
    //! Shared file ownership and locked append callers for cross-crate proofs.

    use std::fs::File;
    use std::io;
    use std::sync::Mutex;

    /// A file and its append offset shared through a single owned mutex.
    #[derive(Debug)]
    pub struct LogResource {
        /// The shared file identity and its exclusive append guard.
        pub file: Mutex<File>,
    }

    #[rustler::resource_impl]
    impl rustler::Resource for LogResource {}

    /// Recover and synchronize the existing log before returning a writable resource.
    ///
    /// # Errors
    /// Propagates opening, reading, truncation and synchronization errors.
    ///
    /// # Panics
    /// Panics if Rustler has not registered the resource type.
    pub fn reopen(max_records: usize) -> io::Result<Option<rustler::ResourceArc<LogResource>>> {
        let mut file = io_protocol::open_readwrite("journal")?;
        let ready = match io_protocol::repair_log(&mut file, max_records) {
            Ok(Some(_values)) => true,
            Ok(None) => false,
            Err(error) => {
                drop(file);
                return Err(error);
            }
        };
        if ready {
            Ok(Some(rustler::ResourceArc::new(LogResource {
                file: Mutex::new(file),
            })))
        } else {
            drop(file);
            Ok(None)
        }
    }
    /// Reopen and repair a log before exposing its shared writable resource.
    ///
    /// # Panics
    /// Panics on I/O failure, the record limit, or an unregistered resource type.
    #[rustler::nif(name = "log_reopen", schedule = "DirtyIo")]
    pub fn reopen_nif(max_records: u32) -> rustler::ResourceArc<LogResource> {
        reopen(max_records as usize)
            .expect("repair existing log")
            .expect("recovery record limit reached")
    }

    /// Append under the shared mutex, including any required short-write rollback.
    ///
    /// # Errors
    /// Propagates seek, write, rollback and synchronization errors without
    /// promising that an unsuccessful append restored the original file.
    ///
    /// # Panics
    /// Recursive acquisition may block or panic; callers must not hold this mutex.
    pub fn append(resource: &rustler::ResourceArc<LogResource>, value: u16) -> io::Result<bool> {
        io_protocol::locked_append_or_rollback(&resource.file, value)
    }

    /// Repair and append while holding the resource's single file mutex.
    ///
    /// # Errors
    /// Propagates repair, append, rollback and synchronization failures.
    ///
    /// # Panics
    /// Recursive acquisition may block or panic; callers must not hold this mutex.
    pub fn repair_append(
        resource: &rustler::ResourceArc<LogResource>,
        max_records: usize,
        value: u16,
    ) -> io::Result<bool> {
        io_protocol::locked_repair_and_append(&resource.file, max_records, value)
    }

    /// Acknowledge only a synchronized repair/append, consuming the decoded owner.
    /// An I/O error or recovery limit returns false without promising rollback.
    #[rustler::nif(name = "log_repair_append", schedule = "DirtyIo")]
    pub fn repair_append_nif(
        resource: rustler::ResourceArc<LogResource>,
        max_records: u32,
        value: u16,
    ) -> bool {
        let result = repair_append(&resource, max_records as usize, value);
        drop(resource);
        match result {
            Ok(accepted) => accepted,
            Err(error) => {
                drop(error);
                false
            }
        }
    }

    /// Create and publish an owned file before transferring it to a shared resource.
    ///
    /// # Errors
    /// Propagates creation or directory synchronization failure, closing any file
    /// already opened on the unsuccessful path.
    ///
    /// # Panics
    /// Panics if Rustler has not registered the resource type.
    pub fn create() -> io::Result<rustler::ResourceArc<LogResource>> {
        let file = io_protocol::create_fresh("journal")?;
        match io_protocol::sync_directory() {
            Ok(()) => Ok(rustler::ResourceArc::new(LogResource {
                file: Mutex::new(file),
            })),
            Err(error) => {
                drop(file);
                Err(error)
            }
        }
    }

    /// Create a fresh named log and synchronize its directory before returning it.
    ///
    /// # Panics
    /// Panics if the file already exists, opening/synchronization fails, or
    /// Rustler has not registered the resource type.
    #[rustler::nif(name = "log_create", schedule = "DirtyIo")]
    pub fn create_nif() -> rustler::ResourceArc<LogResource> {
        create().expect("create synchronized log")
    }

    /// Report successful durable append while consuming the decoded native owner.
    #[rustler::nif(name = "log_append", schedule = "DirtyIo")]
    pub fn append_nif(resource: rustler::ResourceArc<LogResource>, value: u16) -> bool {
        let result = append(&resource, value);
        drop(resource);
        match result {
            Ok(accepted) => accepted,
            Err(error) => {
                drop(error);
                false
            }
        }
    }
}

/// Writes one prefix before applying request policy.
///
/// # Errors
/// Returns two for opening failure and one for a write failure.
///
/// # Panics
/// Rejection panics after the I/O attempt and closes the owned file.
#[cfg(feature = "captured-write")]
#[rustler::nif(name = "checked_write", schedule = "DirtyIo")]
fn checked_write_request(input: rustler::Binary<'_>, accepted: bool) -> Result<u64, u8> {
    let file = match io_protocol::open_readwrite("journal") {
        Ok(file) => file,
        Err(error) => {
            drop(error);
            return Err(2);
        }
    };
    match io_protocol::checked_write(file, input.as_slice(), accepted) {
        Ok(count) => Ok(count as u64),
        Err(error) => Err(error),
    }
}

/// Writes before suspension, then cancels or resumes the actual owned-file future.
///
/// # Errors
/// Returns two for opening failure and one for a write failure.
#[cfg(feature = "async-write")]
#[rustler::nif(name = "write_poll", schedule = "DirtyIo")]
fn write_poll_request(first: u8, second: u8, resume: bool) -> Result<Option<u64>, u8> {
    let file = match io_protocol::open_readwrite("journal") {
        Ok(file) => file,
        Err(error) => {
            drop(error);
            return Err(2);
        }
    };
    match io_protocol::poll_write(file, [first, second], resume) {
        Some(Ok(written)) => Ok(Some(written as u64)),
        Some(Err(error)) => Err(error),
        None => Ok(None),
    }
}

#[cfg(feature = "async-shared-write")]
mod async_log {
    use super::shared_log::LogResource;
    use rustler::ResourceArc;
    use std::sync::Mutex;

    #[rustler::nif(name = "async_log_open", schedule = "DirtyIo")]
    fn open_request() -> rustler::NifResult<ResourceArc<LogResource>> {
        let file = match io_protocol::open_readwrite("journal") {
            Ok(file) => file,
            Err(error) => {
                drop(error);
                return Err(rustler::Error::Atom("open_failed"));
            }
        };
        Ok(ResourceArc::new(LogResource {
            file: Mutex::new(file),
        }))
    }

    #[rustler::nif(name = "async_log_write", schedule = "DirtyIo")]
    fn write_request(
        owner: ResourceArc<LogResource>,
        first: u8,
        second: u8,
        resume: bool,
    ) -> Result<Option<u64>, u8> {
        let reply = io_protocol::poll_locked_write(&owner.file, [first, second], resume);
        drop(owner);
        match reply {
            None => Ok(None),
            Some(Ok(count)) => Ok(Some(count as u64)),
            Some(Err(error)) => Err(error),
        }
    }
    /// Acknowledges a written prefix only after synchronization on resumption.
    ///
    /// # Errors
    /// Returns one for write failure and two for synchronization failure.
    ///
    /// # Panics
    /// Recursive acquisition may block or panic; the verification model rejects it.
    #[cfg(feature = "async-sync")]
    #[rustler::nif(name = "async_log_sync", schedule = "DirtyIo")]
    fn sync_request(
        owner: ResourceArc<LogResource>,
        first: u8,
        second: u8,
        resume: bool,
    ) -> Result<Option<u64>, u8> {
        let reply = io_protocol::poll_locked_sync(&owner.file, [first, second], resume);
        drop(owner);
        match reply {
            None => Ok(None),
            Some(Ok(count)) => Ok(Some(count as u64)),
            Some(Err(error)) => Err(error),
        }
    }

    /// Recovers both words through fresh file and lock state.
    ///
    /// # Errors
    /// Returns three for opening failure and one for seeking or reading failure.
    #[cfg(feature = "async-recovery")]
    #[rustler::nif(name = "async_log_recover", schedule = "DirtyIo")]
    fn recover_request() -> Result<(Option<u16>, Option<u16>), u8> {
        io_protocol::reopen_words("journal")
    }

    /// Reads a word from the same shared file state used by the async writer.
    ///
    /// # Errors
    /// Returns one for seeking or reading failure.
    #[rustler::nif(name = "async_log_read", schedule = "DirtyIo")]
    fn read_request(owner: ResourceArc<LogResource>, offset: u64) -> Result<Option<u16>, u8> {
        let reply = io_protocol::locked_word(&owner.file, offset);
        drop(owner);
        reply
    }

    /// Opens a readable resource whose writes fail without poisoning its mutex.
    ///
    /// # Errors
    /// Returns the raw atom `open_failed` if opening the journal fails.
    ///
    /// # Panics
    /// Panics if Rustler has not registered the resource type.
    #[cfg(feature = "async-readonly")]
    #[rustler::nif(name = "async_log_readonly", schedule = "DirtyIo")]
    fn readonly_request() -> rustler::NifResult<ResourceArc<LogResource>> {
        let file = match io_protocol::open_readonly("journal") {
            Ok(file) => file,
            Err(error) => {
                drop(error);
                return Err(rustler::Error::Atom("open_failed"));
            }
        };
        Ok(ResourceArc::new(LogResource {
            file: Mutex::new(file),
        }))
    }
}

/// Classifies the standard end-of-file kind through the first-party crates.
#[rustler::nif]
fn classify_end_of_file() -> bool {
    io_protocol::truncated_input(std::io::ErrorKind::UnexpectedEof)
}

/// Distinguishes retryable interruption from a truncated protocol input.
#[rustler::nif]
fn classify_interrupted_read() -> bool {
    io_protocol::truncated_input(std::io::ErrorKind::Interrupted)
}

/// Reports retryable opening or reading failures through the first-party crates.
#[rustler::nif(name = "read_retryable", schedule = "DirtyIo")]
fn read_retryable_nif() -> bool {
    io_protocol::read_is_retryable("missing")
}

/// Reads an optional protocol word through the standard exact-read loop.
///
/// # Errors
/// Returns two for opening failure and one for a non-EOF reading failure.
#[rustler::nif(name = "read_exact_word", schedule = "DirtyIo")]
fn read_exact_word_nif() -> Result<Option<u16>, u8> {
    io_protocol::read_exact_optional("input")
}

/// Decodes a word without consuming an optional trailing payload.
/// # Errors
/// Returns one for truncated input.
#[rustler::nif(name = "slice_word")]
fn slice_word_nif(input: rustler::Binary<'_>) -> Result<(u16, u64), u8> {
    io_protocol::parse_packet(input.as_slice())
}

#[cfg(all(unix, feature = "positional-file"))]
mod offset_file;
