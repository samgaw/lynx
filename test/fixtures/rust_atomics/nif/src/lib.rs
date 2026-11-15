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

/// Reacquires the same enum-backed state between two independent chunk updates.
#[rustler::nif(name = "consume_chunks", schedule = "DirtyCpu")]
#[lynx::phase]
fn consume_chunks(budget: u64, first: u64, second: u64) -> (bool, bool, u64) {
    let phase = std::sync::Mutex::new(atomic_core::start_phase(budget));
    let (accepted_first, _) = atomic_analysis::consume_locked(&phase, first);
    let (accepted_second, total) = atomic_analysis::consume_locked(&phase, second);
    (accepted_first, accepted_second, total)
}

/// An owned byte buffer retained by a shared resource.
#[derive(Debug)]
pub struct ByteBuffer {
    pub bytes: Vec<u8>,
}
#[rustler::resource_impl]
impl rustler::Resource for ByteBuffer {}

/// Stores two bytes in a registered resource.
///
/// # Panics
/// Panics if the resource type has not been registered.
#[rustler::nif(name = "buffer_new", schedule = "DirtyCpu")]
#[lynx::buffer]
#[lynx::buffer_copy]
#[expect(
    clippy::vec_init_then_push,
    reason = "Exercise audited vector growth before resource ownership transfer"
)]
fn buffer_new(first: u8, second: u8) -> rustler::ResourceArc<ByteBuffer> {
    let mut bytes = Vec::new();
    bytes.push(first);
    bytes.push(second);
    rustler::ResourceArc::new(ByteBuffer { bytes })
}
/// Observes the same shared byte buffer through a first-party callee.
#[rustler::nif(name = "buffer_length", schedule = "DirtyCpu")]
#[lynx::buffer]
#[lynx::buffer_copy]
#[lynx::locked_copy]
fn buffer_length(buffer: rustler::ResourceArc<ByteBuffer>) -> u64 {
    atomic_analysis::buffer_length(buffer.bytes.as_slice()) as u64
}

/// Reads the leading stored byte through the same shared resource.
#[rustler::nif(name = "buffer_head", schedule = "DirtyCpu")]
#[lynx::buffer]
#[lynx::buffer_copy]
#[lynx::locked_copy]
fn buffer_head(buffer: rustler::ResourceArc<ByteBuffer>) -> u8 {
    atomic_analysis::buffer_head(buffer.bytes.as_slice())
}
/// Consumes an internal Rust owner without exposing a new NIF.
#[lynx::buffer]
#[lynx::buffer_copy]
pub fn buffer_dispose(buffer: rustler::ResourceArc<ByteBuffer>) {
    drop(buffer);
}

/// Retains an owned copy after the binary argument's borrow has ended.
/// # Panics
/// Panics if the resource type has not been registered.
#[rustler::nif(name = "buffer_copy", schedule = "DirtyCpu")]
#[lynx::buffer_copy]
fn buffer_copy(input: rustler::Binary<'_>) -> rustler::ResourceArc<ByteBuffer> {
    rustler::ResourceArc::new(ByteBuffer {
        bytes: atomic_analysis::copy_bytes(input.as_slice()),
    })
}

/// Copies borrowed bytes under a native guard, then transfers the owned buffer.
///
/// # Panics
/// Panics if the resource type has not been registered.
#[rustler::nif(name = "buffer_copy_locked", schedule = "DirtyCpu")]
#[lynx::locked_copy]
fn buffer_copy_locked(input: rustler::Binary<'_>) -> rustler::ResourceArc<ByteBuffer> {
    rustler::ResourceArc::new(ByteBuffer {
        bytes: atomic_analysis::copy_locked(input.as_slice()),
    })
}

/// A persistent shared resource; its mutex owns first-party protocol state.
pub struct SharedBuffer {
    pub state: std::sync::Mutex<atomic_analysis::ReceiveState>,
}

#[rustler::resource_impl]
impl rustler::Resource for SharedBuffer {}

/// Creates registered shared state.
///
/// # Panics
/// Panics if the resource type has not been registered.
#[rustler::nif(name = "shared_new", schedule = "DirtyCpu")]
#[lynx::shared_buffer]
fn shared_new() -> rustler::ResourceArc<SharedBuffer> {
    rustler::ResourceArc::new(SharedBuffer {
        state: std::sync::Mutex::new(atomic_analysis::ReceiveState {
            buffer: atomic_core::BufferState { bytes: Vec::new() },
        }),
    })
}

#[rustler::nif(name = "shared_append", schedule = "DirtyCpu")]
#[lynx::shared_buffer]
fn shared_append(buffer: rustler::ResourceArc<SharedBuffer>, input: rustler::Binary<'_>) -> u64 {
    atomic_analysis::append_state(&buffer.state, input.as_slice())
}

#[rustler::nif(name = "shared_read", schedule = "DirtyCpu")]
#[lynx::shared_buffer]
fn shared_read(buffer: rustler::ResourceArc<SharedBuffer>) -> (u64, u8) {
    atomic_analysis::read_state(&buffer.state)
}

/// Internal root checking final owner cleanup independently of NIF exposure.
#[lynx::shared_buffer]
pub fn shared_release(buffer: rustler::ResourceArc<SharedBuffer>) {
    drop(buffer);
}
