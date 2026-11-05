//! The only crate that exports a NIF.

/// Delegates to the first-party implementation on a dirty CPU scheduler.
#[rustler::nif(name = "restore", schedule = "DirtyCpu")]
fn native_restore(value: bool) -> bool {
    example_analysis::restore(value)
}

rustler::init!("Elixir.LynxWorkspaceExample.Native");
