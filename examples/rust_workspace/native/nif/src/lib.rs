//! The only crate that exports a NIF.

#![feature(register_tool)]
#![register_tool(verify)]

/// Delegates to the first-party implementation on a dirty CPU scheduler.
#[rustler::nif(name = "restore", schedule = "DirtyCpu")]
#[verify::start_from]
fn native_restore(value: bool) -> bool {
    example_analysis::restore(value)
}

rustler::init!("Elixir.LynxWorkspaceExample.Native");
