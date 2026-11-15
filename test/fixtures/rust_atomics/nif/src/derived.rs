//! Derived protocol requests for an actual stateful facade.
use crate::Counter;
use rustler::ResourceArc;

/// Compare-and-replace request represented by a two-field Erlang tuple.
#[derive(rustler::NifTuple)]
pub struct Request {
    expected: u64,
    replacement: u64,
}

/// Composes the native update through both ordinary workspace crates.
pub fn counter_tuple(resource: ResourceArc<Counter>, request: Request) -> (bool, u64) {
    atomic_analysis::try_set(&resource.state, request.expected, request.replacement)
}

#[rustler::nif(name = "atomic_tuple", schedule = "DirtyCpu")]
#[lynx::tuple_decode]
fn tuple(resource: ResourceArc<Counter>, request: Request) -> (bool, u64) {
    counter_tuple(resource, request)
}
