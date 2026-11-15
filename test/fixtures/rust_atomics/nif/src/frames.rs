//! Stateless framing facade over actual library-crate buffer mutations.

#[rustler::nif(name = "frame_summary", schedule = "DirtyCpu")]
#[lynx::frames]
fn summary(input: rustler::Binary<'_>) -> (u8, u64, u64) {
    atomic_analysis::frame_summary(input.as_slice())
}

/// # Panics
/// Panics when position exceeds the decoded input length.
#[rustler::nif(name = "frame_split")]
#[lynx::frames]
fn split(input: rustler::Binary<'_>, position: u16) -> (u64, u64) {
    let mut bytes = atomic_analysis::copy_bytes(input.as_slice());
    let suffix = atomic_core::frames::split_buffer(&mut bytes, position as usize);
    (bytes.len() as u64, suffix.len() as u64)
}
