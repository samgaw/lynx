use std::fs::{self, OpenOptions};
use std::io;
use std::path::PathBuf;
use std::sync::Mutex;
use std::time::{SystemTime, UNIX_EPOCH};

struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

#[test]
fn overlapping_repairs_keep_records_and_release_after_errors() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let path = Scratch(
        std::env::temp_dir().join(format!("lynx-locked-repair-{}-{nonce}", std::process::id())),
    );
    let values = [13u16, 0xffff, 0x1234];
    let prefix = values
        .into_iter()
        .flat_map(io_core::encode_record)
        .collect::<Vec<_>>();
    let mut torn = prefix.clone();
    torn.extend_from_slice(&[7]);
    fs::write(&path.0, torn)?;
    let shared = Mutex::new(OpenOptions::new().read(true).write(true).open(&path.0)?);
    std::thread::scope(|scope| -> io::Result<()> {
        let first = scope.spawn(|| io_protocol::locked_repair(&shared, 4));
        let second = scope.spawn(|| io_protocol::locked_repair(&shared, 4));
        assert_eq!(
            first.join().expect("repair thread panicked")?,
            Some(values.to_vec())
        );
        assert_eq!(
            second.join().expect("repair thread panicked")?,
            Some(values.to_vec())
        );
        Ok(())
    })?;
    assert_eq!(fs::read(&path.0)?, prefix);
    assert!(shared.try_lock().is_ok());

    let read_only = Mutex::new(OpenOptions::new().read(true).open(&path.0)?);
    assert!(io_protocol::locked_repair(&read_only, 4).is_err());
    assert!(read_only.try_lock().is_ok());
    assert_eq!(fs::read(&path.0)?, prefix);
    Ok(())
}
