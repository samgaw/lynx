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

/// Consumes an owned mutex without constructing it in this function.
pub fn mutex_consume_scalar(_mutex: Mutex<u64>) {}

/// Consumes a native mutex whose payload has no destructor behavior.
pub fn mutex_discard_scalar(value: u64) {
    drop(Mutex::new(value));
}

/// Lets the compiler destroy an owned scalar mutex at scope exit.
pub fn mutex_scope_scalar(value: u64) {
    let _mutex = Mutex::new(value);
}

/// Returns a value after the compiler-generated scalar mutex destruction.
pub fn mutex_scope_flag(value: u64) -> bool {
    let _mutex = Mutex::new(value);
    true
}

/// Requires effectful unwinding of a live scalar mutex.
///
/// # Panics
/// Panics when `accepted` is false.
pub fn mutex_assert_scalar(value: u64, accepted: bool) {
    let _mutex = Mutex::new(value);
    assert!(accepted);
}

/// Applies a first-party update and consumes the scalar mutex holding its result.
pub fn mutex_checked_discard(value: u64, amount: u64) -> bool {
    let mut counter = effects_core::Counter { value };
    let changed = effects_core::increment(&mut counter, amount);
    drop(Mutex::new(counter.value));
    changed
}

/// Consumes the mutex before an assertion, leaving no mutex to unwind.
///
/// # Panics
/// Panics when `accepted` is false, after the mutex has been destroyed.
pub fn mutex_dispose_then_assert(value: u64, accepted: bool) {
    {
        let _mutex = Mutex::new(value);
    }
    assert!(accepted);
}

/// Explicitly consumes a newly initialized native mutex.
pub fn mutex_discard(value: u64) {
    drop(Mutex::new(effects_core::Counter { value }));
}

/// Lets the compiler generate destruction at the end of the scope.
pub fn mutex_scope(value: u64) {
    let _mutex = Mutex::new(effects_core::Counter { value });
}

/// Exercises cleanup required after an assertion failure with a live mutex.
///
/// # Panics
/// Panics when `accepted` is false.
pub fn mutex_assert(value: u64, accepted: bool) {
    let _mutex = Mutex::new(effects_core::Counter { value });
    assert!(accepted);
}

/// A payload with observable user-defined destruction, deliberately not admitted.
pub struct PanickingPayload {
    /// Stored value.
    pub value: u64,
}

impl Drop for PanickingPayload {
    fn drop(&mut self) {
        panic!("tracked destruction");
    }
}

/// Exercises a custom payload destructor through the actual standard mutex.
///
/// # Panics
/// Always panics in the payload destructor.
pub fn mutex_discard_custom(value: u64) {
    drop(Mutex::new(PanickingPayload { value }));
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
    #[test]
    #[should_panic(expected = "tracked destruction")]
    fn custom_payload_destruction_is_observable() {
        super::mutex_discard_custom(7);
    }
}
