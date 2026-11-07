//! Actual OS calibration supplements the implementation-linked recovery proofs.
use std::fs;
use std::io;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn recovers_words_and_rejects_incomplete_files() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let scratch = Scratch(std::env::temp_dir().join(format!(
        "lynx-resource-recovery-{}-{nonce}",
        std::process::id()
    )));
    fs::create_dir(&scratch.0)?;
    let path = scratch.0.join("resource");
    let name = path.to_str().expect("temporary path must be UTF-8");
    assert!(effects_native::recover_file_word(name).is_err());
    for bytes in [&[][..], &[7][..]] {
        fs::write(&path, bytes)?;
        assert_eq!(effects_native::recover_file_word(name)?, None);
    }
    for value in [0u16, 1, 4660, u16::MAX] {
        fs::write(&path, value.to_le_bytes())?;
        assert_eq!(effects_native::recover_file_word(name)?, Some(value));
        assert_eq!(effects_native::recover_file_word(name)?, Some(value));
    }
    fs::write(&path, [52, 18, 99])?;
    assert_eq!(effects_native::recover_file_word(name)?, Some(4660));
    Ok(())
}
