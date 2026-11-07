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
