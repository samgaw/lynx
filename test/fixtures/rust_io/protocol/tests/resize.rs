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
