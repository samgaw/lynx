//! Nested tagged requests composed with shared native state.
use crate::Counter;
use rustler::ResourceArc;
#[derive(rustler::NifTuple)]
pub struct Replacement {
    expected: u64,
    replacement: u64,
}
#[derive(rustler::NifTaggedEnum)]
pub enum Command {
    Read,
    Compare(Replacement),
}
pub fn execute(resource: ResourceArc<Counter>, command: Command) -> (bool, u64) {
    match command {
        Command::Read => (false, atomic_core::current(&resource.state)),
        Command::Compare(request) => {
            atomic_analysis::try_set(&resource.state, request.expected, request.replacement)
        }
    }
}
#[rustler::nif(name = "atomic_command", schedule = "DirtyCpu")]
#[lynx::commands]
fn command(resource: ResourceArc<Counter>, input: Command) -> (bool, u64) {
    execute(resource, input)
}
