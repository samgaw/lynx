//! Resource-backed sequence counter using actual cross-crate atomic operations.
#![feature(register_tool)]
#![register_tool(lynx)]
use std::sync::atomic::AtomicU64;

pub struct Counter {
    pub state: AtomicU64,
}

#[rustler::resource_impl]
impl rustler::Resource for Counter {}

pub fn counter_new(value: u64) -> rustler::ResourceArc<Counter> {
    rustler::ResourceArc::new(Counter {
        state: AtomicU64::new(value),
    })
}

pub fn counter_claim(resource: rustler::ResourceArc<Counter>) -> u64 {
    atomic_core::claim(&resource.state)
}

pub fn counter_pair(resource: rustler::ResourceArc<Counter>) -> (u64, u64) {
    atomic_analysis::claim_two(&resource.state)
}

pub fn counter_read(resource: rustler::ResourceArc<Counter>) -> u64 {
    atomic_core::current(&resource.state)
}

/// An internal proof root also checks final-owner cleanup without a VM pin.
#[lynx::atomic]
pub fn counter_cycle(value: u64) -> (u64, u64) {
    counter_pair(counter_new(value))
}

/// Checks the actual panic cleanup path while holding a native resource.
///
/// # Panics
/// Panics when the request is rejected.
pub fn counter_checked(value: u64, accepted: bool) -> (u64, u64) {
    let resource = counter_new(value);
    assert!(accepted);
    counter_pair(resource)
}

#[rustler::nif(name = "atomic_new")]
#[lynx::atomic]
fn create(value: u64) -> rustler::ResourceArc<Counter> {
    counter_new(value)
}

#[rustler::nif(name = "atomic_claim", schedule = "DirtyCpu")]
#[lynx::atomic]
fn claim(resource: rustler::ResourceArc<Counter>) -> u64 {
    counter_claim(resource)
}

#[rustler::nif(name = "atomic_pair", schedule = "DirtyCpu")]
#[lynx::atomic]
fn pair(resource: rustler::ResourceArc<Counter>) -> (u64, u64) {
    counter_pair(resource)
}

#[rustler::nif(name = "atomic_read")]
#[lynx::atomic]
fn read(resource: rustler::ResourceArc<Counter>) -> u64 {
    counter_read(resource)
}

#[rustler::nif(name = "atomic_checked", schedule = "DirtyCpu")]
#[lynx::atomic]
fn checked(value: u64, accepted: bool) -> (u64, u64) {
    counter_checked(value, accepted)
}

rustler::init!("Elixir.LynxAtomicFixture.Native");

/// Deliberately outside captured scalar-tuple output admission.
pub fn unsupported_owner_tuple(value: u64) -> (rustler::ResourceArc<Counter>, u64) {
    (counter_new(value), value)
}

/// Deliberately requires logical local-cell retirement, which is not yet modelled.
pub fn unsupported_discard(value: u64) -> u64 {
    let counter = AtomicU64::new(value);
    atomic_core::claim(&counter)
}
