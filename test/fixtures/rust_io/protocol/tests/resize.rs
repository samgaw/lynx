use std::fs::{self, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

#[test]
fn length_changes_preserve_offsets_prefixes_and_zero_fill() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let path =
        Scratch(std::env::temp_dir().join(format!("lynx-resize-{}-{nonce}", std::process::id())));
    let mut file = OpenOptions::new()
        .create_new(true)
        .read(true)
        .write(true)
        .open(&path.0)?;
    file.write_all(&[1, 2, 3, 4, 5, 6])?;
    io_protocol::resize_then_sync(&file, 4)?;
    assert_eq!(file.stream_position()?, 6);
    assert_eq!(file.metadata()?.len(), 4);
    io_protocol::resize_then_sync(&file, 8)?;
    assert_eq!(file.stream_position()?, 6);
    file.seek(SeekFrom::Start(0))?;
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)?;
    assert_eq!(bytes, [1, 2, 3, 4, 0, 0, 0, 0]);
    let readonly = OpenOptions::new().read(true).open(&path.0)?;
    assert!(io_protocol::resize_then_sync(&readonly, 0).is_err());
    assert_eq!(fs::read(&path.0)?, bytes);
    Ok(())
}

#[test]
fn repair_discards_only_the_examined_partial_tail() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let path =
        Scratch(std::env::temp_dir().join(format!("lynx-repair-{}-{nonce}", std::process::id())));
    let values = [7u16, 0xffff, 0x1234];
    let prefix = values
        .into_iter()
        .flat_map(io_core::encode_record)
        .collect::<Vec<_>>();
    for length in 0..=3 {
        let mut original = prefix.clone();
        original.extend_from_slice(&io_core::encode_record(42)[..length]);
        fs::write(&path.0, &original)?;
        let mut file = OpenOptions::new().read(true).write(true).open(&path.0)?;
        assert_eq!(io_protocol::repair_log(&mut file, 3)?, None);
        assert_eq!(fs::read(&path.0)?, original);
        assert_eq!(
            io_protocol::repair_log(&mut file, 4)?,
            Some(values.to_vec())
        );
        assert_eq!(fs::read(&path.0)?, prefix);
        assert_eq!(
            io_protocol::repair_log(&mut file, 4)?,
            Some(values.to_vec())
        );
        assert!(io_protocol::append_record(&mut file, 42)?);
        assert_eq!(
            io_protocol::recover_log(&mut file, 5)?,
            [7, 0xffff, 0x1234, 42]
        );
    }
    Ok(())
}

#[test]
fn repair_stops_at_an_invalid_record_before_later_valid_records() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let path = Scratch(
        std::env::temp_dir().join(format!("lynx-malformed-{}-{nonce}", std::process::id())),
    );
    let values = [7u16, 9];
    let prefix = values
        .into_iter()
        .flat_map(io_core::encode_record)
        .collect::<Vec<_>>();
    let mut bytes = prefix.clone();
    bytes.extend_from_slice(&[1, 2, 3, 4]);
    bytes.extend_from_slice(&io_core::encode_record(42));
    bytes.extend_from_slice(&io_core::encode_record(u16::MAX));
    bytes.push(7);
    fs::write(&path.0, &bytes)?;
    let mut file = OpenOptions::new().read(true).write(true).open(&path.0)?;
    assert_eq!(io_protocol::recover_log(&mut file, 10)?, values);
    assert_eq!(file.stream_position()?, 12);
    assert_eq!(fs::read(&path.0)?, bytes);
    assert_eq!(io_protocol::repair_log(&mut file, 2)?, None);
    assert_eq!(fs::read(&path.0)?, bytes);
    assert_eq!(
        io_protocol::repair_log(&mut file, 10)?,
        Some(values.to_vec())
    );
    assert_eq!(file.stream_position()?, 12);
    assert_eq!(fs::read(&path.0)?, prefix);
    assert!(io_protocol::append_record(&mut file, 42)?);
    assert_eq!(io_protocol::recover_log(&mut file, 10)?, [7, 9, 42]);
    Ok(())
}

#[test]
fn locked_appends_serialize_shared_file_effects_and_release_after_errors() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let path = Scratch(
        std::env::temp_dir().join(format!("lynx-locked-file-{}-{nonce}", std::process::id())),
    );
    let file = OpenOptions::new()
        .create_new(true)
        .read(true)
        .write(true)
        .open(&path.0)?;
    let mutex = std::sync::Mutex::new(file);
    std::thread::scope(|scope| {
        let first = scope.spawn(|| -> io::Result<()> {
            for value in [1, 3] {
                assert!(io_protocol::locked_append(&mutex, value)?);
            }
            Ok(())
        });
        let second = scope.spawn(|| -> io::Result<()> {
            for value in [2, 4] {
                assert!(io_protocol::locked_append(&mutex, value)?);
            }
            Ok(())
        });
        first.join().expect("first file writer must not panic")?;
        second.join().expect("second file writer must not panic")?;
        Ok::<(), io::Error>(())
    })?;
    let mut guard = mutex.lock().expect("file mutex must remain unpoisoned");
    let mut values = io_protocol::recover_log(&mut guard, 5)?;
    values.sort_unstable();
    assert_eq!(values, [1, 2, 3, 4]);
    assert_eq!(guard.metadata()?.len(), 16);
    drop(guard);
    let readonly = std::sync::Mutex::new(OpenOptions::new().read(true).open(&path.0)?);
    assert!(io_protocol::locked_append(&readonly, 5).is_err());
    assert!(readonly.try_lock().is_ok());
    Ok(())
}

#[cfg(all(
    target_pointer_width = "64",
    any(target_os = "linux", target_os = "macos")
))]
#[test]
fn short_writes_are_rolled_back_before_another_append() -> io::Result<()> {
    const CHILD: &str = "LYNX_SHORT_WRITE_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe()?)
            .args([
                "--exact",
                "short_writes_are_rolled_back_before_another_append",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()?;
        assert!(
            output.status.success(),
            "short-write child failed: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        return Ok(());
    }

    #[repr(C)]
    #[derive(Clone, Copy)]
    struct Limits {
        current: u64,
        maximum: u64,
    }
    unsafe extern "C" {
        fn getrlimit(resource: std::ffi::c_int, limit: *mut Limits) -> std::ffi::c_int;
        fn setrlimit(resource: std::ffi::c_int, limit: *const Limits) -> std::ffi::c_int;
    }
    // RLIMIT_FSIZE is 1 and rlim_t is u64 on these 64-bit targets. Run in an
    // isolated child so the process-wide limit cannot affect parallel tests.
    let mut old = std::mem::MaybeUninit::<Limits>::uninit();
    // SAFETY: the output pointer is aligned and writable for one C rlimit.
    if unsafe { getrlimit(1, old.as_mut_ptr()) } != 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: getrlimit initialized both fields on its successful return.
    let old = unsafe { old.assume_init() };
    let restricted = Limits { current: 6, ..old };
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let path = Scratch(
        std::env::temp_dir().join(format!("lynx-short-write-{}-{nonce}", std::process::id())),
    );
    let mut file = OpenOptions::new()
        .create_new(true)
        .read(true)
        .write(true)
        .open(&path.0)?;
    let prefix = io_core::encode_record(7);
    file.write_all(&prefix)?;
    file.sync_all()?;
    let mutex = std::sync::Mutex::new(file);
    // SAFETY: the limit pointer contains a valid initialized C rlimit. Only
    // this child process is affected; raising the soft limit later stays at
    // the original hard limit.
    if unsafe { setrlimit(1, &restricted) } != 0 {
        return Err(io::Error::last_os_error());
    }
    assert!(!io_protocol::locked_append_or_rollback(&mutex, 9)?);
    let mut guard = mutex
        .lock()
        .expect("short-write rollback must release its guard");
    assert_eq!(guard.metadata()?.len(), 4);
    assert_eq!(guard.stream_position()?, 6);
    assert_eq!(fs::read(&path.0)?, prefix);
    drop(guard);
    // SAFETY: old is the original initialized limit for this same process.
    if unsafe { setrlimit(1, &old) } != 0 {
        return Err(io::Error::last_os_error());
    }
    assert!(io_protocol::locked_append_or_rollback(&mutex, 11)?);
    let mut guard = mutex.lock().expect("full append must release its guard");
    assert_eq!(io_protocol::recover_log(&mut guard, 3)?, [7, 11]);
    Ok(())
}
