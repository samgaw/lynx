//! Publication calibration; operating system execution cannot simulate power loss.
#![cfg(unix)]

use std::fs;
use std::io;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn publishes_in_the_current_directory() -> io::Result<()> {
    if std::env::var_os("LYNX_PUBLICATION_CHILD").is_some() {
        fs::write("a", [7, 0])?;
        let file = fs::OpenOptions::new().read(true).write(true).open("a")?;
        io_protocol::publish_file(file, "a", "b")?;
        assert!(!std::path::Path::new("a").exists());
        assert_eq!(fs::read("b")?, [7, 0]);
        assert_eq!(io_protocol::recover_named_word("b")?, Some(7));
        fs::write("empty", [])?;
        fs::write("truncated", [7])?;
        assert_eq!(io_protocol::recover_named_word("empty")?, None);
        assert_eq!(io_protocol::recover_named_word("truncated")?, None);
        assert!(io_protocol::recover_named_word("missing").is_err());
        assert!(io_protocol::commit_word("c", "d", u16::MAX)?);
        assert_eq!(io_protocol::recover_named_word("d")?, Some(u16::MAX));
        fs::write("busy", [1])?;
        assert!(io_protocol::commit_word("busy", "unused", 0).is_err());
        assert_eq!(fs::read("busy")?, [1]);
        assert!(!std::path::Path::new("unused").exists());
        let write_only = fs::File::create("write-only")?;
        assert!(io_protocol::read_and_close_word(write_only).is_err());
        return Ok(());
    }

    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let scratch = Scratch(
        std::env::temp_dir().join(format!("lynx-publication-{}-{nonce}", std::process::id())),
    );
    fs::create_dir(&scratch.0)?;
    let output = Command::new(std::env::current_exe()?)
        .args([
            "--exact",
            "publishes_in_the_current_directory",
            "--nocapture",
        ])
        .env("LYNX_PUBLICATION_CHILD", "1")
        .current_dir(&scratch.0)
        .output()?;
    assert!(
        output.status.success(),
        "publication child failed: {output:?}"
    );
    Ok(())
}
