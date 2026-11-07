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
