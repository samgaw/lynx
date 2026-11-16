use std::fs::{File, OpenOptions};
use std::future::Future;
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, TryLockError};
use std::task::{Context, Poll, Waker};

static NEXT_FILE: AtomicUsize = AtomicUsize::new(0);

fn shared_file() -> (Mutex<File>, PathBuf) {
    let path = std::env::temp_dir().join(format!(
        "lynx-locked-await-{}-{}",
        std::process::id(),
        NEXT_FILE.fetch_add(1, Ordering::Relaxed)
    ));
    let mut file = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(&path)
        .unwrap();
    file.write_all(&[1]).unwrap();
    file.seek(SeekFrom::Start(0)).unwrap();
    (Mutex::new(file), path)
}

#[test]
fn pending_retains_guard_and_cancellation_unlocks_live_file() {
    let (mutex, path) = shared_file();
    let mut context = Context::from_waker(Waker::noop());
    {
        let mut writer = std::pin::pin!(io_protocol::locked_suspended_write(&mutex, [7, 8]));
        assert_eq!(writer.as_mut().poll(&mut context), Poll::Pending);
        assert!(matches!(mutex.try_lock(), Err(TryLockError::WouldBlock)));
    }
    assert_eq!(
        io_protocol::poll_locked_write(&mutex, [9, 10], true),
        Some(Ok(2))
    );
    let mut guard = mutex.try_lock().unwrap();
    assert_eq!(guard.stream_position().unwrap(), 4);
    guard.seek(SeekFrom::Start(0)).unwrap();
    let mut bytes = Vec::new();
    guard.read_to_end(&mut bytes).unwrap();
    assert_eq!(bytes, [7, 8, 9, 10]);
    drop(guard);
    drop(mutex);
    std::fs::remove_file(path).unwrap();
}

#[test]
fn poisoned_guard_is_recovered_and_shared_reads_observe_both_writes() {
    let (mutex, path) = shared_file();
    assert!(std::panic::catch_unwind(|| {
        let _guard = mutex.lock().unwrap();
        panic!("poison fixture mutex");
    })
    .is_err());
    assert_eq!(io_protocol::poll_locked_write(&mutex, [7, 8], false), None);
    assert_eq!(
        io_protocol::poll_locked_write(&mutex, [9, 10], true),
        Some(Ok(2))
    );
    assert!(mutex.is_poisoned());
    assert_eq!(io_protocol::locked_word(&mutex, 0), Ok(Some(2055)));
    assert_eq!(io_protocol::locked_word(&mutex, 2), Ok(Some(2569)));
    assert_eq!(io_protocol::locked_word(&mutex, 4), Ok(None));
    drop(mutex);
    std::fs::remove_file(path).unwrap();
}

#[test]
fn concurrent_cancelled_and_completed_writers_preserve_both_words() {
    let (mutex, path) = shared_file();
    let start = std::sync::Barrier::new(3);
    std::thread::scope(|scope| {
        let cancelled = scope.spawn(|| {
            start.wait();
            io_protocol::poll_locked_write(&mutex, [7, 8], false)
        });
        let completed = scope.spawn(|| {
            start.wait();
            io_protocol::poll_locked_write(&mutex, [9, 10], true)
        });
        start.wait();
        assert_eq!(cancelled.join().unwrap(), None);
        assert_eq!(completed.join().unwrap(), Some(Ok(2)));
    });
    let first = io_protocol::locked_word(&mutex, 0).unwrap().unwrap();
    let second = io_protocol::locked_word(&mutex, 2).unwrap().unwrap();
    assert!(matches!((first, second), (2055, 2569) | (2569, 2055)));
    drop(mutex);
    std::fs::remove_file(path).unwrap();
}

#[test]
fn failed_readonly_writes_release_guard_and_preserve_readable_file() {
    let (original, path) = shared_file();
    drop(original);
    std::fs::write(&path, [7, 8]).unwrap();
    let file = io_protocol::open_readonly(path.to_str().unwrap()).unwrap();
    let mutex = Mutex::new(file);
    assert_eq!(io_protocol::poll_locked_write(&mutex, [9, 10], false), None);
    assert_eq!(
        io_protocol::poll_locked_write(&mutex, [9, 10], true),
        Some(Err(1))
    );
    assert!(!mutex.is_poisoned());
    assert!(mutex.try_lock().is_ok());
    assert_eq!(io_protocol::locked_word(&mutex, 0), Ok(Some(2055)));
    assert_eq!(std::fs::read(&path).unwrap(), [7, 8]);
    drop(mutex);
    std::fs::remove_file(path).unwrap();
}
