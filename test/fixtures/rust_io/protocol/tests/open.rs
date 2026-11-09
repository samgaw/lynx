use std::fs;
use std::io::{self, Read, Seek, Write};
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn separate_opens_share_contents_and_keep_independent_read_only_offsets() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let directory =
        Scratch(std::env::temp_dir().join(format!("lynx-open-{}-{nonce}", std::process::id())));
    fs::create_dir(&directory.0)?;
    let path = directory.0.join("input");
    fs::write(&path, [1, 2, 3])?;
    let path = path.to_str().expect("test temporary path must be UTF-8");
    let (mut first, mut second) = io_protocol::open_pair(path)?;
    let mut byte = [0];
    first.read_exact(&mut byte)?;
    assert_eq!(byte, [1]);
    assert_eq!(first.stream_position()?, 1);
    assert_eq!(second.stream_position()?, 0);
    second.read_exact(&mut byte)?;
    assert_eq!(byte, [1]);
    assert!(first.write_all(&[9]).is_err());
    assert_eq!(first.stream_position()?, 1);
    assert_eq!(fs::read(path)?, [1, 2, 3]);
    assert!(io_protocol::open_readonly(&format!("{path}.missing")).is_err());
    Ok(())
}

#[test]
fn exclusive_creation_is_writable_and_preserves_an_existing_file() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let directory =
        Scratch(std::env::temp_dir().join(format!("lynx-create-{}-{nonce}", std::process::id())));
    fs::create_dir(&directory.0)?;
    let path = directory.0.join("fresh");
    let path = path.to_str().expect("test temporary path must be UTF-8");
    let mut file = io_protocol::create_fresh(path)?;
    file.write_all(&[4, 5])?;
    assert_eq!(file.stream_position()?, 2);
    file.rewind()?;
    let mut bytes = [0; 2];
    file.read_exact(&mut bytes)?;
    assert_eq!(bytes, [4, 5]);
    assert!(io_protocol::create_fresh(path).is_err());
    assert_eq!(fs::read(path)?, [4, 5]);
    Ok(())
}

#[test]
fn writable_reopen_retains_records_and_does_not_create_missing_files() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let directory =
        Scratch(std::env::temp_dir().join(format!("lynx-reopen-{}-{nonce}", std::process::id())));
    fs::create_dir(&directory.0)?;
    let path = directory.0.join("journal");
    let path = path.to_str().expect("test temporary path must be UTF-8");
    fs::write(path, io_core::encode_record(13))?;

    let mut file = io_protocol::open_readwrite(path)?;
    let mut record = [0; 4];
    file.read_exact(&mut record)?;
    assert_eq!(
        record,
        io_core::encode_record(13),
        "reopen truncated the log"
    );
    file.rewind()?;
    file.write_all(&[13])?;
    drop(file);

    assert!(io_protocol::reopen_then_append(path, 19)?);
    let expected = [io_core::encode_record(13), io_core::encode_record(19)].concat();
    assert_eq!(
        fs::read(path)?,
        expected,
        "reopen did not retain both records"
    );

    let missing = directory.0.join("missing");
    let missing_path = missing.to_str().expect("test temporary path must be UTF-8");
    assert!(io_protocol::open_readwrite(missing_path).is_err());
    assert!(io_protocol::reopen_then_append(missing_path, 19).is_err());
    assert!(
        !missing.exists(),
        "opening an existing log created a new file"
    );
    Ok(())
}
