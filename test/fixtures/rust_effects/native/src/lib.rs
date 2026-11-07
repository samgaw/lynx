//! Real native APIs used to measure extraction support, not assumed models.
use std::sync::Mutex;

/// Runs a complete critical section in another first-party workspace crate.
pub fn locked_increment(mutex: &Mutex<effects_core::Counter>, amount: u64) -> bool {
    effects_core::locked_increment(mutex, amount)
}

/// Reads a borrowed guard through another first-party crate.
pub fn guard_read(guard: &std::sync::MutexGuard<'_, effects_core::Counter>) -> u64 {
    effects_core::read_guard(guard)
}

/// Updates a borrowed guard through another first-party crate.
pub fn guard_increment(
    guard: &mut std::sync::MutexGuard<'_, effects_core::Counter>,
    amount: u64,
) -> bool {
    effects_core::increment_guard(guard, amount)
}

/// Transfers a guard to another crate to update and release its shared payload.
pub fn guard_update_release(
    guard: std::sync::MutexGuard<'_, effects_core::Counter>,
    amount: u64,
) -> bool {
    effects_core::update_release(guard, amount)
}

/// Releases a guard through the first-party callee.
pub fn guard_release(guard: std::sync::MutexGuard<'_, effects_core::Counter>) {
    effects_core::release_guard(guard);
}

/// Uses the compiler-generated normal guard drop in another first-party crate.
pub fn guard_update_scope(
    guard: std::sync::MutexGuard<'_, effects_core::Counter>,
    amount: u64,
) -> bool {
    effects_core::update_scope(guard, amount)
}

/// Composes an owning update/release with a new acquisition across crate calls.
pub fn guard_update_reacquire<'a>(
    guard: std::sync::MutexGuard<'a, effects_core::Counter>,
    mutex: &'a Mutex<effects_core::Counter>,
    amount: u64,
) -> (
    bool,
    std::sync::LockResult<std::sync::MutexGuard<'a, effects_core::Counter>>,
) {
    let changed = effects_core::update_release(guard, amount);
    (changed, effects_core::acquire_counter(mutex))
}

/// Releases ownership before an assertion, leaving no guard to poison on failure.
///
/// # Panics
/// Panics when the request is rejected, after normal release has completed.
pub fn guard_release_then_assert(
    guard: std::sync::MutexGuard<'_, effects_core::Counter>,
    accepted: bool,
) {
    drop(guard);
    assert!(accepted);
}

/// Requires updated payload propagation and guard poisoning during unwind.
///
/// # Panics
/// Panics when the request is rejected while the guard is still owned.
pub fn guard_owned_then_assert(
    mut guard: std::sync::MutexGuard<'_, effects_core::Counter>,
    amount: u64,
    accepted: bool,
) {
    effects_core::increment_guard(&mut guard, amount);
    assert!(accepted);
    drop(guard);
}

/// Exercises mutation whose updated borrow would be lost on panic.
///
/// # Panics
/// Panics when the request is rejected. Verification rejects this failure path.
pub fn guard_increment_then_assert(
    guard: &mut std::sync::MutexGuard<'_, effects_core::Counter>,
    amount: u64,
    accepted: bool,
) {
    effects_core::increment_guard(guard, amount);
    assert!(accepted);
}

/// A guard contained in another first-party type still carries a mutable borrow.
pub struct GuardEnvelope<'a> {
    /// Guard owned by the envelope.
    pub guard: std::sync::MutexGuard<'a, effects_core::Counter>,
}

/// Exercises the same unsupported failure path through a nested guard field.
///
/// # Panics
/// Panics when the request is rejected, after updating the borrowed payload.
pub fn guard_envelope_then_assert(envelope: &mut GuardEnvelope<'_>, amount: u64, accepted: bool) {
    effects_core::increment_guard(&mut envelope.guard, amount);
    assert!(accepted);
}

/// Shared resource containing the state protected by the native mutex.
pub struct CounterResource {
    state: Mutex<effects_core::Counter>,
}

/// Constructs an owned payload whose compiler drop glue releases its mutex.
pub fn owned_counter_payload(value: u64) -> CounterResource {
    CounterResource {
        state: Mutex::new(effects_core::Counter { value }),
    }
}

#[rustler::resource_impl]
impl rustler::Resource for CounterResource {}

/// Destructor-free resource with a payload defined in another workspace crate.
pub struct ScalarResource {
    counter: effects_core::Counter,
}

#[rustler::resource_impl]
impl rustler::Resource for ScalarResource {}

/// Allocates a resource after its type has been registered by the native loader.
///
/// # Panics
/// Panics when the loader has not registered the resource type.
pub fn scalar_resource_new(value: u64) -> rustler::ResourceArc<ScalarResource> {
    rustler::ResourceArc::new(ScalarResource {
        counter: effects_core::Counter { value },
    })
}

/// Retains the same shared allocation with another Rust ownership token.
pub fn scalar_resource_clone(
    resource: &rustler::ResourceArc<ScalarResource>,
) -> rustler::ResourceArc<ScalarResource> {
    resource.clone()
}

/// Reads through the resource's shared dereference and a first-party callee.
pub fn scalar_resource_read(resource: &rustler::ResourceArc<ScalarResource>) -> u64 {
    effects_core::counter_value(&resource.counter)
}

/// Releases the original handle, observes its retained alias, then releases it.
///
/// # Panics
/// Panics when the loader has not registered the resource type.
pub fn scalar_resource_cycle(value: u64) -> u64 {
    let first = scalar_resource_new(value);
    let retained = scalar_resource_clone(&first);
    drop(first);
    let observed = scalar_resource_read(&retained);
    drop(retained);
    observed
}

/// Uses compiler-generated scope cleanup for the final retained handle.
///
/// # Panics
/// Panics when the loader has not registered the resource type.
pub fn scalar_resource_scope(value: u64) -> u64 {
    let first = scalar_resource_new(value);
    let retained = scalar_resource_clone(&first);
    drop(first);
    scalar_resource_read(&retained)
}

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

/// Retains the same mutex-containing resource without copying its shared state.
pub fn resource_clone(
    resource: &rustler::ResourceArc<CounterResource>,
) -> rustler::ResourceArc<CounterResource> {
    resource.clone()
}

/// Updates the shared resource through the cross-crate poison-recovering section.
pub fn resource_locked_increment(
    resource: &rustler::ResourceArc<CounterResource>,
    amount: u64,
) -> bool {
    effects_core::locked_increment(&resource.state, amount)
}

/// Reads protected shared state through the first-party guard implementation.
pub fn resource_locked_value(resource: &rustler::ResourceArc<CounterResource>) -> u64 {
    let guard = effects_core::recover_guard(resource.state.lock());
    let value = effects_core::read_guard(&guard);
    effects_core::release_guard(guard);
    value
}

/// Consumes one Rust ownership token, running payload cleanup on final release.
pub fn resource_release(resource: rustler::ResourceArc<CounterResource>) {
    drop(resource);
}

/// Retains an alias, releases the original, updates shared state, and reclaims it.
///
/// # Panics
/// Panics when the loader has not registered the resource type.
pub fn resource_cycle(value: u64, amount: u64) -> bool {
    let first = resource_new(value);
    let retained = resource_clone(&first);
    resource_release(first);
    let changed = resource_locked_increment(&retained, amount);
    resource_release(retained);
    changed
}

/// Calls the actual first-party Future implementation, retaining its mutable state.
pub fn poll_paused(
    future: std::pin::Pin<&mut effects_core::PausedCounter>,
    context: &mut std::task::Context<'_>,
) -> std::task::Poll<u64> {
    std::future::Future::poll(future, context)
}

/// Polls an Unpin first-party future twice, or cancels after its first Pending.
///
/// # Panics
/// A caller-provided waker callback may panic.
pub fn drive_paused_counter(
    value: u64,
    cancel_after_pending: bool,
    context: &mut std::task::Context<'_>,
) -> Option<u64> {
    use std::future::Future;
    use std::task::Poll;
    let mut future = effects_core::paused_counter(value);
    match std::pin::Pin::new(&mut future).poll(context) {
        Poll::Ready(value) => Some(value),
        Poll::Pending if cancel_after_pending => None,
        Poll::Pending => match std::pin::Pin::new(&mut future).poll(context) {
            Poll::Ready(value) => Some(value),
            Poll::Pending => None,
        },
    }
}

/// Completes on its first poll through a first-party dependency.
pub async fn immediate_increment(value: u64) -> u64 {
    effects_core::saturating_increment(value)
}

/// Suspends while retaining the actual future from another first-party crate.
pub async fn suspended_increment(value: u64) -> u64 {
    effects_core::paused_counter(value).await
}

/// Keeps an owned mutex across suspension, requiring saved-field drop support.
pub async fn owned_suspending(value: u64) -> u64 {
    let mutex = Mutex::new(value);
    let result = effects_core::paused_counter(value).await;
    drop(mutex);
    result
}

/// Retains a mutated guard across suspension and commits it on release or cancellation.
///
/// # Panics
/// Recursive mutex acquisition may panic or block.
#[expect(
    clippy::await_holding_lock,
    reason = "Verification fixture intentionally retains the guard across a Pending poll"
)]
pub async fn guarded_suspending(mutex: &Mutex<effects_core::Counter>, amount: u64) -> bool {
    let mut guard = effects_core::recover_guard(mutex.lock());
    let changed = effects_core::increment_guard(&mut guard, amount);
    let _progress = effects_core::paused_counter(amount).await;
    effects_core::release_guard(guard);
    changed
}

/// Retains a shared resource owner across a cross-crate suspension.
///
/// # Panics
/// Recursive mutex acquisition may panic or block.
pub async fn resource_suspending(
    resource: rustler::ResourceArc<CounterResource>,
    amount: u64,
) -> bool {
    let _progress = effects_core::paused_counter(amount).await;
    let changed = resource_locked_increment(&resource, amount);
    resource_release(resource);
    changed
}

/// Completes a shared-resource update on its first poll and releases its owner.
///
/// # Panics
/// Recursive mutex acquisition may panic or block.
pub async fn resource_immediate(
    resource: rustler::ResourceArc<CounterResource>,
    amount: u64,
) -> bool {
    let changed = resource_locked_increment(&resource, amount);
    resource_release(resource);
    changed
}

/// Polls the actual resource future, then destroys its completed frame.
///
/// # Panics
/// Recursive mutex acquisition may panic or block.
pub fn poll_ready_resource(
    resource: rustler::ResourceArc<CounterResource>,
    amount: u64,
    context: &mut std::task::Context<'_>,
) -> std::task::Poll<bool> {
    use std::future::Future;
    std::pin::pin!(resource_immediate(resource, amount)).poll(context)
}

/// Cancels the actual suspended resource future when its local scope ends.
///
/// # Panics
/// A caller-provided waker callback may panic.
pub fn poll_cancel_resource(
    resource: rustler::ResourceArc<CounterResource>,
    amount: u64,
    context: &mut std::task::Context<'_>,
) -> std::task::Poll<bool> {
    use std::future::Future;
    std::pin::pin!(resource_suspending(resource, amount)).poll(context)
}

/// Retains an owned capture, exercising cancellation cleanup rejection.
pub async fn owned_immediate(value: Vec<u8>) -> usize {
    value.len()
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

/// Transfers the owner to another first-party crate, including its failure path.
///
/// # Panics
/// Panics when `accepted` is false, after the callee has consumed the mutex.
pub fn mutex_release_checked(value: u64, accepted: bool) {
    effects_core::release_checked(Mutex::new(value), accepted);
}

/// Transfers an owner to a first-party callee whose assertion can unwind.
///
/// # Panics
/// Panics when `accepted` is false, after the callee performs unwind cleanup.
pub fn mutex_assert_release(value: u64, accepted: bool) {
    effects_core::assert_then_release(Mutex::new(value), accepted);
}

/// Exercises separate assertion failure paths while one scalar owner is live.
///
/// # Panics
/// Panics when either flag is false, destroying the owned mutex during unwind.
pub fn mutex_two_assertions(value: u64, first: bool, second: bool) {
    let _mutex = Mutex::new(value);
    assert!(first);
    assert!(second);
}

/// Exercises the guard update/destruction boundary independently of ResourceArc.
///
/// # Panics
/// Panics if the mutex is poisoned.
pub fn mutex_guarded_increment(mutex: &Mutex<effects_core::Counter>, amount: u64) -> bool {
    let mut guard = mutex.lock().unwrap();
    effects_core::increment(&mut guard, amount)
}

/// Composes actual first-party acquisition without exposing guards as NIFs.
///
/// # Panics
/// Native recursive acquisition can panic or block; verification rejects it.
pub fn mutex_acquire(
    mutex: &Mutex<effects_core::Counter>,
) -> std::sync::LockResult<std::sync::MutexGuard<'_, effects_core::Counter>> {
    effects_core::acquire_counter(mutex)
}

/// Requires guard destruction independently of unwrap or dereference support.
///
/// # Panics
/// Native recursive acquisition can panic or block; verification rejects it.
pub fn mutex_acquire_and_drop(mutex: &Mutex<effects_core::Counter>) {
    let _owned_result = effects_core::acquire_counter(mutex);
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
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    use std::task::{Context, Poll, Wake, Waker};
    #[derive(Default)]
    struct Notification(AtomicBool);
    impl Wake for Notification {
        fn wake(self: Arc<Self>) {
            self.0.store(true, Ordering::Release);
        }
        fn wake_by_ref(self: &Arc<Self>) {
            self.0.store(true, Ordering::Release);
        }
    }

    #[test]
    fn bounded_driver_polls_the_actual_dependency_and_observes_cancellation() {
        for value in [0, 7, u64::MAX] {
            for cancel in [false, true] {
                let notification = Arc::new(Notification::default());
                let waker = Waker::from(notification.clone());
                let mut context = Context::from_waker(&waker);
                assert_eq!(
                    super::drive_paused_counter(value, cancel, &mut context),
                    if cancel {
                        None
                    } else {
                        Some(value.saturating_add(1))
                    }
                );
                assert!(notification.0.load(Ordering::Acquire));
            }
        }
    }

    #[test]
    fn suspended_guard_commits_mutations_on_cancellation_and_completion() {
        use std::future::Future;
        for (value, amount) in [(4, 3), (u64::MAX, 1)] {
            for cancel in [false, true] {
                let mutex = std::sync::Mutex::new(effects_core::Counter { value });
                let mut future = Box::pin(super::guarded_suspending(&mutex, amount));
                let mut context = Context::from_waker(Waker::noop());
                assert_eq!(future.as_mut().poll(&mut context), Poll::Pending);
                assert!(matches!(
                    mutex.try_lock(),
                    Err(std::sync::TryLockError::WouldBlock)
                ));
                if !cancel {
                    assert_eq!(
                        future.as_mut().poll(&mut context),
                        Poll::Ready(value.checked_add(amount).is_some())
                    );
                }
                drop(future);
                assert_eq!(
                    mutex.lock().unwrap().value,
                    value.checked_add(amount).unwrap_or(value)
                );
            }
        }
    }

    #[test]
    fn paused_future_preserves_progress_across_explicit_polls() {
        for value in [0, 7, u64::MAX] {
            let notification = Arc::new(Notification::default());
            let waker = Waker::from(Arc::clone(&notification));
            let mut future = std::pin::pin!(effects_core::paused_counter(value));
            let mut context = Context::from_waker(&waker);
            assert_eq!(
                super::poll_paused(future.as_mut(), &mut context),
                Poll::Pending
            );
            assert!(!future.waiting);
            assert!(notification.0.load(Ordering::Acquire));
            assert_eq!(future.counter.value, value);
            assert_eq!(
                super::poll_paused(future.as_mut(), &mut context),
                Poll::Ready(value.saturating_add(1))
            );
        }
    }

    #[test]
    fn compiler_future_suspends_resumes_and_rejects_repolling() {
        use std::future::Future;
        for value in [0, 7, u64::MAX] {
            let notification = Arc::new(Notification::default());
            let waker = Waker::from(Arc::clone(&notification));
            let mut future = std::pin::pin!(super::suspended_increment(value));
            let mut context = Context::from_waker(&waker);
            assert_eq!(future.as_mut().poll(&mut context), Poll::Pending);
            assert!(notification.0.load(Ordering::Acquire));
            assert_eq!(
                future.as_mut().poll(&mut context),
                Poll::Ready(value.saturating_add(1))
            );
            assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                future.as_mut().poll(&mut context)
            }))
            .is_err());
        }
    }

    #[test]
    fn immediate_future_completes_and_rejects_repolling() {
        use std::future::Future;
        use std::task::{Context, Poll, Waker};

        for value in [0, 7, u64::MAX] {
            let mut future = std::pin::pin!(super::immediate_increment(value));
            let mut context = Context::from_waker(Waker::noop());
            assert_eq!(
                future.as_mut().poll(&mut context),
                Poll::Ready(value.saturating_add(1))
            );
            assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                future.as_mut().poll(&mut context)
            }))
            .is_err());
        }
    }

    #[test]
    fn complete_critical_section_rejects_overflow_without_poisoning() {
        let mutex = std::sync::Mutex::new(effects_core::Counter { value: u64::MAX });
        assert!(!super::locked_increment(&mutex, 1));
        assert!(!mutex.is_poisoned());
        assert_eq!(
            mutex
                .try_lock()
                .expect("critical section must release")
                .value,
            u64::MAX
        );
    }

    #[test]
    fn complete_critical_section_retains_existing_poison() {
        let mutex = std::sync::Mutex::new(effects_core::Counter { value: 7 });
        let failed = std::panic::catch_unwind(|| {
            let mut guard = mutex.lock().expect("fresh mutex must not be poisoned");
            guard.value = 9;
            panic!("poison before recovery");
        });
        assert!(failed.is_err());
        assert!(super::locked_increment(&mutex, 4));
        assert!(mutex.is_poisoned());
        let guard = match mutex.try_lock() {
            Err(std::sync::TryLockError::Poisoned(error)) => error.into_inner(),
            _ => panic!("recovery must release the lock and retain the poison flag"),
        };
        assert_eq!(guard.value, 13);
    }

    #[test]
    fn native_threads_complete_both_extracted_critical_sections() {
        let mutex = std::sync::Mutex::new(effects_core::Counter { value: 7 });
        std::thread::scope(|scope| {
            let first = scope.spawn(|| super::locked_increment(&mutex, 3));
            let second = scope.spawn(|| super::locked_increment(&mutex, 4));
            assert!(first.join().expect("first critical section must finish"));
            assert!(second.join().expect("second critical section must finish"));
        });
        assert_eq!(
            mutex.try_lock().expect("both workers must release").value,
            14
        );
    }

    #[test]
    fn owned_update_is_visible_after_release() {
        let mutex = std::sync::Mutex::new(effects_core::Counter { value: 7 });
        let guard = mutex.lock().expect("fresh lock must be available");
        assert!(super::guard_update_release(guard, 5));
        let guard = mutex.try_lock().expect("update must release the lock");
        assert_eq!(guard.value, 12);
        assert!(!super::guard_update_release(guard, u64::MAX));
        let guard = mutex
            .try_lock()
            .expect("rejection must also release the lock");
        assert_eq!(guard.value, 12);
        assert!(super::guard_update_scope(guard, 2));
        let guard = mutex.try_lock().expect("scope exit must release the lock");
        assert_eq!(guard.value, 14);
        let (changed, acquired) = super::guard_update_reacquire(guard, &mutex, 3);
        assert!(changed);
        let guard = acquired.expect("release must permit reacquisition");
        assert_eq!(guard.value, 17);
        super::guard_release(guard);
        assert!(!mutex.is_poisoned());
    }

    #[test]
    fn borrowed_guard_update_preserves_rejected_state() {
        let mutex = std::sync::Mutex::new(effects_core::Counter { value: 7 });
        let mut guard = mutex.lock().expect("fresh mutex must be unlocked");
        assert!(super::guard_increment(&mut guard, 3));
        assert_eq!(super::guard_read(&guard), 10);
        assert!(!super::guard_increment(&mut guard, u64::MAX));
        assert_eq!(super::guard_read(&guard), 10);
        assert!(mutex.try_lock().is_err());
        drop(guard);
        assert_eq!(mutex.lock().expect("release must preserve state").value, 10);
    }

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

    #[test]
    fn cross_crate_acquisition_holds_the_actual_guard() {
        let mutex = std::sync::Mutex::new(effects_core::Counter { value: 7 });
        let guard = match super::mutex_acquire(&mutex) {
            Ok(guard) => guard,
            Err(_) => panic!("a fresh mutex must not be poisoned"),
        };
        assert_eq!(guard.value, 7);
        assert!(mutex.try_lock().is_err());
        drop(guard);
        assert!(mutex.try_lock().is_ok());
    }

    #[test]
    fn poisoned_acquisition_still_owns_the_actual_guard() {
        let mutex = std::sync::Mutex::new(effects_core::Counter { value: 7 });
        let failed = std::panic::catch_unwind(|| {
            let mut guard = mutex.lock().unwrap();
            guard.value = 19;
            panic!("poison the mutex");
        });
        assert!(failed.is_err());
        let guard = match super::mutex_acquire(&mutex) {
            Ok(_) => panic!("acquisition must report the poisoned mutex"),
            Err(error) => error.into_inner(),
        };
        assert_eq!(guard.value, 19);
        assert!(matches!(
            mutex.try_lock(),
            Err(std::sync::TryLockError::WouldBlock)
        ));
    }
}

/// Allocates, updates and consumes a scalar mutex through a first-party callee.
///
/// # Panics
/// Recursive acquisition can panic or block; no recursive acquisition is made here.
pub fn mutex_locked_scalar(value: u64, amount: u64) -> bool {
    let mutex = Mutex::new(value);
    let changed = effects_core::locked_scalar_increment(&mutex, amount);
    drop(mutex);
    changed
}

#[cfg(test)]
mod runtime_nif_tests {
    #[test]
    fn scalar_critical_section_checks_overflow_and_releases() {
        assert!(super::mutex_locked_scalar(7, 3));
        assert!(!super::mutex_locked_scalar(u64::MAX, 1));
        assert!(super::mutex_locked_scalar(u64::MAX, 0));
    }
}

/// Rustler exports exercising the native runtime through ordinary scalar codecs.
#[cfg(feature = "nif")]
mod facade {
    /// Runs the Rust-owned lifecycle; formal adapters still require a loader model.
    ///
    /// # Panics
    /// Panics when the resource type has not been registered.
    #[cfg(feature = "resource-nif")]
    #[rustler::nif(name = "retained", schedule = "DirtyCpu")]
    fn resource_retained(value: u64) -> u64 {
        super::scalar_resource_cycle(value)
    }

    /// Preserves the checked result across allocation and normal destruction.
    #[rustler::nif(name = "checked", schedule = "DirtyCpu")]
    fn checked(value: u64, amount: u64) -> bool {
        super::mutex_locked_scalar(value, amount)
    }

    /// Uses compiler unwind cleanup for a destructor-free first-party payload.
    ///
    /// # Panics
    /// Panics when `accepted` is false, after compiler-generated cleanup.
    #[cfg(feature = "payload-nif")]
    #[rustler::nif(name = "released_struct", schedule = "DirtyCpu")]
    fn payload_release(value: u64, accepted: bool) -> bool {
        super::mutex_assert(value, accepted);
        true
    }

    /// Raises only after normal destruction has completed.
    ///
    /// # Panics
    /// Panics when `accepted` is false, after consuming the native mutex.
    #[rustler::nif]
    fn released(value: u64, accepted: bool) -> bool {
        super::mutex_dispose_then_assert(value, accepted);
        true
    }
}

/// Creates an immutable resource returned to the VM.
///
/// # Panics
/// Panics if called before the native loader registers ScalarResource.
#[cfg(feature = "resource-handles")]
#[rustler::nif]
pub fn resource_create(value: u64) -> rustler::ResourceArc<ScalarResource> {
    scalar_resource_new(value)
}

/// Reads a VM-held resource through the first-party implementation.
#[cfg(feature = "resource-handles")]
#[rustler::nif]
pub fn resource_value(resource: rustler::ResourceArc<ScalarResource>) -> u64 {
    scalar_resource_read(&resource)
}

/// The second argument exercises decoder failure after acquiring a Rust owner.
#[cfg(feature = "resource-handles")]
#[rustler::nif]
pub fn resource_checked(resource: rustler::ResourceArc<ScalarResource>, accepted: bool) -> u64 {
    if accepted {
        scalar_resource_read(&resource)
    } else {
        0
    }
}

/// Returns a resource whose payload owns a native mutex.
///
/// # Panics
/// Panics if its resource type is not registered by the loader.
#[cfg(feature = "locked-resource-handles")]
#[rustler::nif(name = "counter_new")]
pub fn locked_resource_create(value: u64) -> rustler::ResourceArc<CounterResource> {
    resource_new(value)
}

/// Updates a VM-held resource, consuming only this call's decoded Rust owner.
#[cfg(feature = "locked-resource-handles")]
#[rustler::nif(name = "counter_add", schedule = "DirtyCpu")]
pub fn locked_resource_add(resource: rustler::ResourceArc<CounterResource>, amount: u64) -> bool {
    let changed = resource_locked_increment(&resource, amount);
    resource_release(resource);
    changed
}

/// Reads the current shared value and releases this call's temporary owner.
#[cfg(feature = "locked-resource-handles")]
#[rustler::nif(name = "counter_value")]
pub fn locked_resource_read(resource: rustler::ResourceArc<CounterResource>) -> u64 {
    let value = resource_locked_value(&resource);
    resource_release(resource);
    value
}

#[cfg(feature = "nif")]
rustler::init!("Elixir.LynxEffectsFixture.Native");

/// Completes the actual compiler future with a standard no-op task context.
///
/// # Panics
/// Recursive mutex acquisition may panic or block.
#[cfg(feature = "future-resource-handles")]
#[rustler::nif(name = "counter_poll_add", schedule = "DirtyCpu")]
pub fn locked_resource_poll_add(
    resource: rustler::ResourceArc<CounterResource>,
    amount: u64,
) -> bool {
    let mut context = std::task::Context::from_waker(std::task::Waker::noop());
    match poll_ready_resource(resource, amount, &mut context) {
        std::task::Poll::Ready(changed) => changed,
        std::task::Poll::Pending => false,
    }
}

/// Cancels a Pending resource future using its actual compiler destructor.
///
/// This discards notifications and never waits for or promises async progress.
#[cfg(feature = "future-resource-handles")]
#[rustler::nif(name = "counter_poll_cancel", schedule = "DirtyCpu")]
pub fn locked_resource_poll_cancel(
    resource: rustler::ResourceArc<CounterResource>,
    amount: u64,
) -> bool {
    let mut context = std::task::Context::from_waker(std::task::Waker::noop());
    matches!(
        poll_cancel_resource(resource, amount, &mut context),
        std::task::Poll::Pending
    )
}

/// Explicitly polls the actual owned resource future twice.
///
/// # Panics
/// A caller-provided waker may panic; recursive mutex acquisition may panic or block.
pub fn finish_resource(
    resource: rustler::ResourceArc<CounterResource>,
    amount: u64,
    context: &mut std::task::Context<'_>,
) -> std::task::Poll<bool> {
    use std::future::Future;
    let mut future = std::pin::pin!(resource_suspending(resource, amount));
    match future.as_mut().poll(context) {
        std::task::Poll::Pending => future.as_mut().poll(context),
        ready => ready,
    }
}
