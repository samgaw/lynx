//! Derived record requests for native state updates.
use crate::Counter;
use rustler::ResourceArc;

/// A map-shaped compare-and-replace request.
#[derive(rustler::NifMap)]
pub struct MapRequest {
    expected: u64,
    replacement: u64,
}
/// A tagged struct request whose module is checked by the actual derive.
#[derive(rustler::NifStruct)]
#[module = "LynxRecordFixture.Request"]
pub struct StructRequest {
    expected: u64,
    replacement: u64,
}

/// Update shared state through the two ordinary library crates.
pub fn update_map(resource: ResourceArc<Counter>, request: MapRequest) -> (bool, u64) {
    atomic_analysis::try_set(&resource.state, request.expected, request.replacement)
}
/// Compose the same update with the tagged request representation.
pub fn update_struct(resource: ResourceArc<Counter>, request: StructRequest) -> (bool, u64) {
    atomic_analysis::try_set(&resource.state, request.expected, request.replacement)
}
#[rustler::nif(name = "atomic_map", schedule = "DirtyCpu")]
#[lynx::records]
fn map(resource: ResourceArc<Counter>, request: MapRequest) -> (bool, u64) {
    update_map(resource, request)
}
#[rustler::nif(name = "atomic_struct")]
#[lynx::records]
fn record(resource: ResourceArc<Counter>, request: StructRequest) -> (bool, u64) {
    update_struct(resource, request)
}
