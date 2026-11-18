//! Cursor-preserving byte updates through one VM-owned descriptor.
use rustler::{Error, NifResult, ResourceArc};
use std::fs::File;

#[derive(Debug)]
pub struct OffsetFile {
    file: File,
}

#[rustler::resource_impl]
impl rustler::Resource for OffsetFile {}

/// Open the existing fixture file without truncation.
#[rustler::nif(name = "open_slots", schedule = "DirtyIo")]
fn open_nif() -> NifResult<ResourceArc<OffsetFile>> {
    match io_protocol::open_readwrite("slots") {
        Ok(file) => Ok(ResourceArc::new(OffsetFile { file })),
        Err(error) => {
            drop(error);
            Err(Error::RaiseAtom("open_failed"))
        }
    }
}

/// Acknowledge one byte only after a complete, synchronized write.
#[rustler::nif(name = "patch_at", schedule = "DirtyIo")]
fn patch_nif(resource: ResourceArc<OffsetFile>, offset: u64, value: u8) -> bool {
    let reply = io_protocol::positional::patch(&resource.file, offset, &[value]);
    drop(resource);
    match reply {
        Ok(count) => count == 1,
        Err(error) => {
            drop(error);
            false
        }
    }
}

/// Return the byte at the explicit offset, or no byte on EOF or an I/O error.
#[rustler::nif(name = "observe_at", schedule = "DirtyIo")]
fn observe_nif(resource: ResourceArc<OffsetFile>, offset: u64) -> Option<u8> {
    let mut bytes = [0];
    let reply = io_protocol::positional::observe(&resource.file, offset, &mut bytes);
    drop(resource);
    match reply {
        Ok(1) => {
            let [value] = bytes;
            Some(value)
        }
        Ok(_) => None,
        Err(error) => {
            drop(error);
            None
        }
    }
}

/// Return a complete little-endian record, or no record on a read failure.
#[cfg(feature = "positional-exact-read")]
#[rustler::nif(name = "observe_word_at", schedule = "DirtyIo")]
fn observe_word_nif(resource: ResourceArc<OffsetFile>, offset: u64) -> Option<u16> {
    let reply = io_protocol::positional::observe_word(&resource.file, offset);
    drop(resource);
    match reply {
        Ok(word) => Some(word),
        Err(error) => {
            drop(error);
            None
        }
    }
}

/// Acknowledge a whole byte range only after the last write is synchronized.
#[cfg(feature = "positional-write-all")]
#[rustler::nif(name = "patch_all_at", schedule = "DirtyIo")]
fn patch_all_nif(
    resource: ResourceArc<OffsetFile>,
    offset: u64,
    bytes: rustler::Binary<'_>,
) -> bool {
    let reply =
        io_protocol::positional::write_all_and_sync(&resource.file, bytes.as_slice(), offset);
    drop(resource);
    match reply {
        Ok(()) => true,
        Err(error) => {
            drop(error);
            false
        }
    }
}
