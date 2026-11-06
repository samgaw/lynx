//! Real native APIs used to measure extraction support, not assumed models.
use std::sync::Mutex;

/// Shared resource containing the state protected by the native mutex.
pub struct CounterResource {
    state: Mutex<effects_core::Counter>,
}

#[rustler::resource_impl]
impl rustler::Resource for CounterResource {}

/// Allocates the actual Rustler resource. Requires Rustler resource registration.
pub fn resource_new(value: u64) -> rustler::ResourceArc<CounterResource> {
    rustler::ResourceArc::new(CounterResource {
        state: Mutex::new(effects_core::Counter { value }),
    })
}

/// Calls the first-party transition under the actual standard-library mutex.
///
/// # Panics
/// Panics if the mutex is poisoned.
pub fn resource_increment(resource: &rustler::ResourceArc<CounterResource>, amount: u64) -> bool {
    effects_core::increment(&mut resource.state.lock().unwrap(), amount)
}

/// Awaits an actual Rust coroutine, exercising constructor and await lowering.
pub async fn async_increment(value: u64) -> u64 {
    async { value.saturating_add(1) }.await
}

/// Composes two first-party updates, retaining a successful first update if the
/// second increment is rejected because it would overflow.
pub fn increment_twice(counter: &mut effects_core::Counter, first: u64, second: u64) -> bool {
    if effects_core::increment(counter, first) {
        effects_core::increment(counter, second)
    } else {
        false
    }
}

/// Returns a nonzero value unchanged.
///
/// # Panics
/// Panics when the value is zero.
pub fn require_nonzero(value: u64) -> u64 {
    // Use the compiler-generated assertion payload; formatting is outside this probe.
    assert!(value != 0);
    value
}

/// Adds one using the compiler's checked arithmetic.
///
/// # Panics
/// Panics on overflow when overflow checks are enabled.
pub fn checked_next(value: u64) -> u64 {
    value + 1
}
