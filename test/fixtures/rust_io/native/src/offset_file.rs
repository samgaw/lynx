//! Cursor-preserving byte updates through one VM-owned descriptor.
use rustler::ResourceArc;
use std::fs::{File, OpenOptions};

#[derive(Debug)]
pub struct OffsetFile {
    file: File,
}

#[rustler::resource_impl]
impl rustler::Resource for OffsetFile {}

/// Open the fixture file for native calibration.
#[rustler::nif(name = "open_slots", schedule = "DirtyIo")]
fn open_nif() -> ResourceArc<OffsetFile> {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .open("slots")
        .expect("open fixture slots");
    ResourceArc::new(OffsetFile { file })
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
