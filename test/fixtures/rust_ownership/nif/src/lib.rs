//! Rustler facade for actual cross-crate destruction.
#![feature(register_tool)]
#![register_tool(verify)]
#![register_tool(lynx)]

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

/// Observes a borrowed guard's scope-exit mutation through two workspace crates.
#[cfg(feature = "borrowed-guard")]
#[rustler::nif]
#[verify::start_from]
fn borrowed_flip(value: bool) -> bool {
    ownership_app::scoped_flip(value)
}

/// Observes a composed borrowed operation, including its panic cleanup.
///
/// # Panics
/// Propagates rejection after executing both first-party guard destructors.
#[cfg(feature = "captured-unwind")]
#[rustler::nif(name = "captured_value", schedule = "DirtyCpu")]
#[lynx::captured]
fn captured(value: bool, accepted: bool) -> bool {
    let mut first = value;
    let mut second = false;
    ownership_app::compose(&mut first, &mut second, accepted);
    first
}
