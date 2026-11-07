use std::fmt;
use std::io;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

#[derive(Debug)]
struct ObservableError(Arc<AtomicUsize>);

impl fmt::Display for ObservableError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("observable error")
    }
}

impl std::error::Error for ObservableError {}

impl Drop for ObservableError {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

#[test]
fn cleanup_consumes_os_errors_and_runs_custom_payload_destructors() {
    let cleanups: [fn(io::Error); 2] = [
        io_core::discard_io_error,
        io_core::discard_io_error_implicit,
    ];
    let dropped = Arc::new(AtomicUsize::new(0));
    for cleanup in cleanups {
        cleanup(io::Error::from_raw_os_error(2));
        cleanup(io::Error::other(ObservableError(Arc::clone(&dropped))));
    }
    assert_eq!(dropped.load(Ordering::SeqCst), 2);
}
