//! Calibration of the directory operations; this cannot simulate power loss.
#![cfg(unix)]

#[test]
fn directory_sync_and_scope_cleanup_complete() -> std::io::Result<()> {
    io_protocol::sync_directory()?;
    io_protocol::close_directory()?;
    Ok(())
}
