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

/// Builds the first-party state under its checked transition before initializing
/// an unlocked mutex. Rejected increments preserve the original payload.
pub fn mutex_new_incremented(value: u64, amount: u64) -> (bool, Mutex<effects_core::Counter>) {
    let mut counter = effects_core::Counter { value };
    let changed = effects_core::increment(&mut counter, amount);
    (changed, Mutex::new(counter))
}

/// Initializes distinct mutexes containing the two given first-party states.
pub fn mutex_pair(
    first: u64,
    second: u64,
) -> (Mutex<effects_core::Counter>, Mutex<effects_core::Counter>) {
    (
        Mutex::new(effects_core::Counter { value: first }),
        Mutex::new(effects_core::Counter { value: second }),
    )
}

/// Keeps a generic payload, exercising the current explicit codec restriction.
pub fn mutex_generic<T>(value: T) -> Mutex<T> {
    Mutex::new(value)
}

/// Keeps a borrowed payload; ownership tracking is required before heap admission.
pub fn mutex_borrowed(value: &u64) -> Mutex<&u64> {
    Mutex::new(value)
}

/// Initializes a nested first-party payload without flattening its type identity.
pub fn mutex_snapshot(value: u64, enabled: bool) -> Mutex<effects_core::Snapshot> {
    Mutex::new(effects_core::Snapshot {
        enabled,
        counter: effects_core::Counter { value },
    })
}

#[cfg(test)]
mod tests {
    use super::mutex_new_incremented;

    #[test]
    fn mutex_initialization_contains_the_checked_update() {
        let (changed, mutex) = mutex_new_incremented(5, 7);
        assert!(changed);
        assert!(!mutex.is_poisoned());
        let contents = mutex.try_lock().expect("fresh mutex must be unlocked");
        assert_eq!(contents.value, 12);
    }

    #[test]
    fn rejected_update_initializes_the_original_value() {
        let (changed, mutex) = mutex_new_incremented(u64::MAX, 1);
        assert!(!changed);
        assert!(!mutex.is_poisoned());
        let contents = mutex.try_lock().expect("fresh mutex must be unlocked");
        assert_eq!(contents.value, u64::MAX);
    }
}
