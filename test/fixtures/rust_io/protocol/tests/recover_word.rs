use std::fs::{self, File, OpenOptions};
use std::io::{self, Seek, SeekFrom};
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn acknowledged_bytes_survive_reopening_and_recovery_rewinds() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let directory = Scratch(
        std::env::temp_dir().join(format!("lynx-recover-word-{}-{nonce}", std::process::id())),
    );
    fs::create_dir(&directory.0)?;
    let path = directory.0.join("record");
    let mut file = OpenOptions::new()
        .create_new(true)
        .read(true)
        .write(true)
        .open(&path)?;
    assert_eq!(io_protocol::write_then_sync(&mut file, &[0x80, 0xff])?, 2);
    assert_eq!(io_core::seek_from(&mut file, SeekFrom::End(-1))?, 1);
    assert_eq!(io_core::seek_from(&mut file, SeekFrom::Current(-1))?, 0);
    assert!(io_core::seek_from(&mut file, SeekFrom::Current(-1)).is_err());
    assert_eq!(file.stream_position()?, 0);
    io_core::seek_to(&mut file, 20)?;
    assert_eq!(file.metadata()?.len(), 2);
    assert_eq!(io_protocol::recover_word(&mut file)?, Some(0xff80));
    assert_eq!(file.stream_position()?, 2);
    assert_eq!(io_protocol::recover_word(&mut file)?, Some(0xff80));
    drop(file);
    let mut reopened = File::open(&path)?;
    assert_eq!(io_protocol::recover_word(&mut reopened)?, Some(0xff80));
    drop(reopened);
    for bytes in [vec![], vec![0x80]] {
        fs::write(&path, bytes)?;
        let mut truncated = File::open(&path)?;
        io_core::seek_to(&mut truncated, 20)?;
        assert_eq!(io_protocol::recover_word(&mut truncated)?, None);
    }
    Ok(())
}
