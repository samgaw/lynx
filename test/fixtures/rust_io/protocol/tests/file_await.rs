use std::fs::{self, OpenOptions};
use std::future::Future;
use std::io;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::task::{Context, Poll, Wake, Waker};
use std::time::{SystemTime, UNIX_EPOCH};

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

struct Notifications(AtomicUsize);

impl Wake for Notifications {
    fn wake(self: Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }

    fn wake_by_ref(self: &Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

fn scratch() -> io::Result<Scratch> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let directory = Scratch(
        std::env::temp_dir().join(format!("lynx-file-await-{}-{nonce}", std::process::id())),
    );
    fs::create_dir(&directory.0)?;
    Ok(directory)
}

#[test]
fn cancellation_and_completion_keep_the_write_that_precedes_suspension() -> io::Result<()> {
    let directory = scratch()?;
    let path = directory.0.join("input");
    for resume in [false, true] {
        fs::write(&path, [1])?;
        let file = OpenOptions::new().write(true).open(&path)?;
        let notifications = Arc::new(Notifications(AtomicUsize::new(0)));
        let waker = Waker::from(notifications.clone());
        let mut context = Context::from_waker(&waker);
        {
            let mut writer = std::pin::pin!(io_protocol::suspended_write(file, [7, 8]));
            assert_eq!(writer.as_mut().poll(&mut context), Poll::Pending);
            assert_eq!(notifications.0.load(Ordering::SeqCst), 1);
            assert_eq!(fs::read(&path)?, [7, 8]);
            if resume {
                assert_eq!(writer.as_mut().poll(&mut context), Poll::Ready(Ok(2)));
                assert_eq!(notifications.0.load(Ordering::SeqCst), 1);
            }
        }
        assert_eq!(fs::read(&path)?, [7, 8]);
    }
    Ok(())
}

#[test]
fn unstarted_drop_and_failed_write_do_not_modify_the_file() -> io::Result<()> {
    let directory = scratch()?;
    let path = directory.0.join("input");
    fs::write(&path, [1])?;
    let file = OpenOptions::new().write(true).open(&path)?;
    drop(io_protocol::suspended_write(file, [7, 8]));
    assert_eq!(fs::read(&path)?, [1]);
    let readonly = std::fs::File::open(&path)?;
    assert_eq!(
        io_protocol::poll_write(readonly, [7, 8], true),
        Some(Err(1))
    );
    assert_eq!(fs::read(&path)?, [1]);
    Ok(())
}
