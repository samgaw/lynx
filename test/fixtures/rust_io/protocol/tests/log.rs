use std::fs::{self, File, OpenOptions};
use std::io::{self, Seek};
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn appends_retain_previous_records_and_recovery_respects_the_limit() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let directory =
        Scratch(std::env::temp_dir().join(format!("lynx-log-{}-{nonce}", std::process::id())));
    fs::create_dir(&directory.0)?;
    let path = directory.0.join("log");
    let mut file = OpenOptions::new()
        .create_new(true)
        .read(true)
        .write(true)
        .open(&path)?;
    let values = [0u16, 0xffff, 0x1234, 0xff00, 0x8000];
    for value in values {
        io_core::seek_to(&mut file, 0)?;
        assert!(io_protocol::append_record(&mut file, value)?);
    }
    assert_eq!(file.metadata()?.len(), 20);
    for limit in 0..=6 {
        assert_eq!(
            io_protocol::recover_log(&mut file, limit)?,
            values[..limit.min(5)]
        );
        assert_eq!(file.stream_position()?, (limit.min(5) * 4) as u64);
    }
    drop(file);
    let mut reopened = File::open(&path)?;
    assert_eq!(io_protocol::recover_log(&mut reopened, usize::MAX)?, values);
    drop(reopened);
    let complete = values
        .into_iter()
        .flat_map(io_core::encode_record)
        .collect::<Vec<_>>();
    for length in 0..=3 {
        let mut bytes = complete.clone();
        bytes.extend_from_slice(&io_core::encode_record(42)[..length]);
        fs::write(&path, bytes)?;
        assert_eq!(
            io_protocol::recover_log(&mut File::open(&path)?, usize::MAX)?,
            values
        );
    }
    let mut malformed = complete;
    malformed.extend_from_slice(&[1, 2, 3, 4]);
    fs::write(&path, malformed)?;
    assert_eq!(
        io_protocol::recover_log(&mut File::open(&path)?, usize::MAX)?,
        values
    );
    let mut unreadable = OpenOptions::new().write(true).open(&path)?;
    assert!(io_protocol::recover_log(&mut unreadable, 1).is_err());
    Ok(())
}
