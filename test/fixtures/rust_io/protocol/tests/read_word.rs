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
fn words_require_two_bytes_and_preserve_the_following_suffix() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let directory = Scratch(
        std::env::temp_dir().join(format!("lynx-read-word-{}-{nonce}", std::process::id())),
    );
    fs::create_dir(&directory.0)?;
    let path = directory.0.join("input");
    for bytes in [vec![], vec![0x80], vec![0x80, 0xff, 0x12]] {
        fs::write(&path, &bytes)?;
        let mut file = File::open(&path)?;
        let expected = if bytes.len() < 2 { None } else { Some(0xff80) };
        assert_eq!(io_protocol::read_word(&mut file)?, expected);
        assert_eq!(file.stream_position()?, bytes.len().min(2) as u64);
    }
    let mut unreadable = OpenOptions::new().write(true).open(&path)?;
    assert!(io_protocol::read_word(&mut unreadable).is_err());
    assert_eq!(unreadable.stream_position()?, 0);
    Ok(())
}
