use effects_core::Counter;
use effects_native::{cancel_guarded, finish_guarded};
use std::sync::Mutex;
use std::task::{Context, Poll, Waker};

#[test]
fn completion_commits_the_saved_guard() {
    let mutex = Mutex::new(Counter { value: 7 });
    let mut context = Context::from_waker(Waker::noop());
    assert_eq!(finish_guarded(&mutex, 3, &mut context), Poll::Ready(true));
    assert_eq!(
        mutex
            .into_inner()
            .expect("completion releases an unpoisoned guard")
            .value,
        10
    );
}

#[test]
fn cancellation_commits_the_saved_guard() {
    let mutex = Mutex::new(Counter { value: 7 });
    let mut context = Context::from_waker(Waker::noop());
    assert!(cancel_guarded(&mutex, 3, &mut context));
    assert_eq!(
        mutex
            .into_inner()
            .expect("cancellation releases an unpoisoned guard")
            .value,
        10
    );
}

#[test]
fn overflow_preserves_the_saved_guard_payload() {
    let mutex = Mutex::new(Counter { value: u64::MAX });
    let mut context = Context::from_waker(Waker::noop());
    assert_eq!(finish_guarded(&mutex, 1, &mut context), Poll::Ready(false));
    assert_eq!(
        mutex
            .into_inner()
            .expect("overflow releases an unpoisoned guard")
            .value,
        u64::MAX
    );
}
