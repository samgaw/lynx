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
fn fresh_records_reject_truncation_and_zero_new_tearing() -> io::Result<()> {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("test clock must be after the Unix epoch")
        .as_nanos();
    let directory = Scratch(
        std::env::temp_dir().join(format!("lynx-fresh-record-{}-{nonce}", std::process::id())),
    );
    fs::create_dir(&directory.0)?;
    let path = directory.0.join("record");
    for value in [0, 1, 0x00ff, 0xff00, 0x1234, 0x8000, 0xffff] {
        let encoded = io_core::encode_record(value);
        assert_eq!(&encoded[..2], &value.to_le_bytes());
        assert_eq!(&encoded[2..], &(!value).to_le_bytes());
        for length in 0..4 {
            fs::write(&path, &encoded[..length])?;
            let mut truncated = File::open(&path)?;
            assert_eq!(io_protocol::recover_record(&mut truncated)?, None);
        }
        for mask in 0u8..16 {
            let torn = std::array::from_fn::<_, 4, _>(|index| {
                if mask & (1 << index) == 0 {
                    0
                } else {
                    encoded[index]
                }
            });
            fs::write(&path, torn)?;
            let mut file = File::open(&path)?;
            io_core::seek_to(&mut file, 20)?;
            let recovered = io_protocol::recover_record(&mut file)?;
            assert!(
                recovered.is_none() || recovered == Some(value),
                "value={value} mask={mask}"
            );
            assert_eq!(file.stream_position()?, 4);
        }
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .truncate(true)
            .open(&path)?;
        assert!(io_protocol::write_record(&mut file, value)?);
        drop(file);
        assert_eq!(
            io_protocol::recover_record(&mut File::open(&path)?)?,
            Some(value)
        );
    }
    Ok(())
}
