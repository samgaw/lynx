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

/// Executes a checked critical section and its actual compiler cleanup.
///
/// # Panics
/// Rejection releases the poisoned guard and disposes the local mutex.
#[cfg(feature = "guard-unwind")]
#[rustler::nif(name = "guarded_value", schedule = "DirtyCpu")]
#[lynx::guard_unwind]
fn guarded(value: bool, accepted: bool) -> bool {
    ownership_app::local_guard_panic(value, accepted)
}

/// Immutable payload whose Rust ownership tokens can be released during panic.
#[cfg(feature = "resource-unwind")]
#[derive(Debug)]
pub struct UnwindResource {
    pub value: bool,
}

#[cfg(feature = "resource-unwind")]
#[rustler::resource_impl]
impl rustler::Resource for UnwindResource {}

/// Runs the cross-crate transition and consumes its retained owner on either exit.
///
/// # Panics
/// Rejection propagates after releasing this resource owner.
#[cfg(feature = "resource-unwind")]
pub fn checked_resource_inner(
    resource: rustler::ResourceArc<UnwindResource>,
    accepted: bool,
) -> bool {
    let mut value = resource.value;
    ownership_app::checked_value(&mut value, accepted);
    value
}

/// Retains the resource across a fallible first-party operation.
///
/// # Panics
/// Rejection releases the retained and original Rust owners before NIF conversion.
#[cfg(feature = "resource-unwind")]
#[rustler::nif(name = "resource_checked", schedule = "DirtyCpu")]
#[lynx::resource_unwind]
fn checked_resource(resource: rustler::ResourceArc<UnwindResource>, accepted: bool) -> bool {
    let retained = resource.clone();
    checked_resource_inner(retained, accepted)
}

/// Supplies native handles for runtime checks; not a selected verification root.
#[cfg(feature = "resource-unwind")]
#[rustler::nif]
fn resource_seed(value: bool) -> rustler::ResourceArc<UnwindResource> {
    rustler::ResourceArc::new(UnwindResource { value })
}

/// Creates and consumes an owner around the actual cross-crate computation.
///
/// # Panics
/// Registration failure or rejection propagates after applicable owner cleanup.
#[cfg(feature = "resource-unwind")]
pub fn create_checked_resource(value: bool, accepted: bool) -> bool {
    let resource = rustler::ResourceArc::new(UnwindResource { value });
    checked_resource_inner(resource, accepted)
}

/// Keeps another owned cell live across construction and both exceptional exits.
///
/// # Panics
/// Registration failure or rejection disposes the resource and unrelated mutex.
#[cfg(feature = "resource-unwind")]
#[lynx::resource_create]
pub fn create_with_mutex(mutex: std::sync::Mutex<bool>, value: bool, accepted: bool) -> bool {
    let resource = rustler::ResourceArc::new(UnwindResource { value });
    let result = checked_resource_inner(resource, accepted);
    drop(mutex);
    result
}

/// Allocates its own resource before invoking the checked computation.
///
/// # Panics
/// Registration failure and rejection are converted by the generated NIF wrapper.
#[cfg(feature = "resource-unwind")]
#[rustler::nif(name = "resource_created", schedule = "DirtyCpu")]
#[lynx::resource_create]
fn created(value: bool, accepted: bool) -> bool {
    create_checked_resource(value, accepted)
}
