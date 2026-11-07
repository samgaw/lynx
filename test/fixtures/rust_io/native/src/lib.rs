//! Rustler facade for a first-party filesystem publication protocol.

/// Publish a complete word and report whether it was acknowledged.
#[rustler::nif(name = "commit", schedule = "DirtyIo")]
fn commit_nif(value: u16) -> bool {
    io_protocol::commit_ack(value)
}

rustler::init!("Elixir.LynxIoFixture.Native");
