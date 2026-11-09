//! Actual OS calibration supplements the implementation-linked recovery proofs.
use std::fs;
use std::io;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn scratch() -> io::Result<Scratch> {
    static NEXT_SCRATCH: AtomicU64 = AtomicU64::new(0);
    loop {
        let nonce = NEXT_SCRATCH.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "lynx-resource-recovery-{}-{nonce}",
            std::process::id()
        ));
        match fs::create_dir(&path) {
            Ok(()) => return Ok(Scratch(path)),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
}

#[test]
fn recovers_words_and_rejects_incomplete_files() -> io::Result<()> {
    let scratch = scratch()?;
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

#[test]
fn checked_recovery_rejects_torn_and_incomplete_records() -> io::Result<()> {
    let scratch = scratch()?;
    let path = scratch.0.join("resource");
    let name = path.to_str().expect("temporary path must be UTF-8");
    assert!(effects_native::recover_file_record(name).is_err());
    fs::write(&path, [52, 0, 203, 237])?;
    assert_eq!(effects_native::recover_file_word(name)?, Some(52));
    assert_eq!(effects_native::recover_file_record(name)?, None);
    for value in [0u16, 1, 4660, u16::MAX] {
        let record = effects_core::encode_record(value);
        fs::write(&path, record)?;
        assert_eq!(effects_native::recover_file_record(name)?, Some(value));
        for length in 0..4 {
            fs::write(&path, &record[..length])?;
            assert_eq!(effects_native::recover_file_record(name)?, None);
        }
        for mask in 0..16 {
            let torn = std::array::from_fn::<_, 4, _>(|index| {
                if mask & (1 << index) == 0 {
                    0
                } else {
                    record[index]
                }
            });
            fs::write(&path, torn)?;
            if let Some(found) = effects_native::recover_file_record(name)? {
                assert_eq!(found, value);
            }
        }
    }
    Ok(())
}
