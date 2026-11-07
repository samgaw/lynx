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
