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
