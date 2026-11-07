#![cfg(unix)]

use std::fs;
use std::io::{self, Read};
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn replacement_keeps_open_inodes_and_same_inode_names_survive() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let directory =
        Scratch(std::env::temp_dir().join(format!("lynx-rename-{}-{nonce}", std::process::id())));
    fs::create_dir(&directory.0)?;
    let source = directory.0.join("source");
    let target = directory.0.join("target");
    fs::write(&source, b"new")?;
    fs::write(&target, b"old")?;
    let mut previous = fs::File::open(&target)?;
    let source = source.to_str().expect("test temporary path must be UTF-8");
    let target = target.to_str().expect("test temporary path must be UTF-8");
    io_protocol::rename_visible(source, target)?;
    assert!(!std::path::Path::new(source).exists());
    assert_eq!(fs::read(target)?, b"new");
    let mut old_contents = Vec::new();
    previous.read_to_end(&mut old_contents)?;
    assert_eq!(old_contents, b"old");
    fs::hard_link(target, source)?;
    io_protocol::rename_visible(source, target)?;
    assert_eq!(fs::read(source)?, b"new");
    assert_eq!(fs::read(target)?, b"new");
    assert!(io_protocol::rename_visible(&format!("{source}.missing"), target).is_err());
    assert_eq!(fs::read(target)?, b"new");
    Ok(())
}
