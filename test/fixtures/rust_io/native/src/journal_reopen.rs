//! Typed Rustler failures for opening or recovering a named journal.

use crate::shared_log::{reopen, LogResource};
use rustler::{Error, NifResult, ResourceArc};

/// Reopen a named journal, returning ownership of the writable resource.
///
/// # Errors
/// Raises `record_limit` if the scanner fills its record budget, or
/// `journal_io` if a filesystem operation fails.
#[rustler::nif(name = "log_try_reopen", schedule = "DirtyIo")]
fn try_reopen(max_records: u32) -> NifResult<ResourceArc<LogResource>> {
    match reopen(max_records as usize) {
        Ok(Some(resource)) => Ok(resource),
        Ok(None) => Err(Error::RaiseAtom("record_limit")),
        Err(error) => {
            drop(error);
            Err(Error::RaiseAtom("journal_io"))
        }
    }
}
