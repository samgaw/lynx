//! Resource-backed sequence counter using actual cross-crate atomic operations.
#![feature(register_tool)]
#![register_tool(lynx)]

pub mod commands;
pub mod decoding;
pub mod derived;
pub mod encoding;
pub mod records;
pub mod scalars;
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
#[lynx::compare]
#[lynx::returned]
#[lynx::decoded]
#[lynx::tuple_decode]
#[lynx::encoded]
#[lynx::records]
#[lynx::scalars]
#[lynx::commands]
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
#[lynx::compare]
#[lynx::returned]
#[lynx::decoded]
#[lynx::tuple_decode]
#[lynx::encoded]
#[lynx::records]
#[lynx::scalars]
#[lynx::commands]
fn read(resource: rustler::ResourceArc<Counter>) -> u64 {
    counter_read(resource)
}

#[rustler::nif(name = "atomic_checked", schedule = "DirtyCpu")]
#[lynx::atomic]
fn checked(value: u64, accepted: bool) -> (u64, u64) {
    counter_checked(value, accepted)
}

pub fn counter_replace(
    resource: rustler::ResourceArc<Counter>,
    expected: u64,
    replacement: u64,
) -> (bool, u64) {
    atomic_analysis::try_set(&resource.state, expected, replacement)
}

#[rustler::nif(name = "atomic_replace", schedule = "DirtyCpu")]
#[lynx::compare]
fn compare(
    resource: rustler::ResourceArc<Counter>,
    expected: u64,
    replacement: u64,
) -> (bool, u64) {
    counter_replace(resource, expected, replacement)
}

/// Retains the completed atomic update on both return errors and panics.
///
/// # Panics
/// Panics for mode four after the update.
pub fn counter_result(
    resource: rustler::ResourceArc<Counter>,
    mode: u64,
) -> rustler::NifResult<u64> {
    let previous = atomic_core::claim(&resource.state);
    match mode {
        0 => Ok(previous),
        1 => Err(rustler::Error::BadArg),
        2 => Err(rustler::Error::Atom("rejected")),
        3 => Err(rustler::Error::RaiseAtom("rust_panicked")),
        _ => {
            assert!(mode != 4);
            Err(rustler::Error::RaiseAtom("denied"))
        }
    }
}

#[rustler::nif(name = "atomic_result", schedule = "DirtyCpu")]
#[lynx::returned]
fn returned(resource: rustler::ResourceArc<Counter>, mode: u64) -> rustler::NifResult<u64> {
    counter_result(resource, mode)
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

/// Creates signed native state, updates it across crates, then destroys its owner.
#[rustler::nif(name = "signed_adjust", schedule = "DirtyCpu")]
#[lynx::signed]
fn signed_adjust(value: i64, delta: i64) -> (bool, i64) {
    let balance = std::sync::Mutex::new(atomic_core::Balance { value });
    atomic_analysis::locked_adjust(&balance, delta)
}
