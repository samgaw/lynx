//! Rustler facade for actual cross-crate destruction.
#![feature(register_tool)]
#![register_tool(verify)]

/// Consumes an owned first-party value before returning.
///
/// # Panics
/// Panics when the extracted destructor rejects code seven.
#[rustler::nif(name = "checked_code", schedule = "DirtyCpu")]
#[verify::start_from]
fn checked(code: u64) -> bool {
    ownership_app::run(code);
    true
}

/// Consumes a scalar using the same generic first-party consumer.
#[rustler::nif(name = "scalar_code")]
#[verify::start_from]
fn scalar(code: u64) -> bool {
    ownership_app::run_scalar(code);
    true
}

rustler::init!("Elixir.LynxOwnershipFixture.Native");
