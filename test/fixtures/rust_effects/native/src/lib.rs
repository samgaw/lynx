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
