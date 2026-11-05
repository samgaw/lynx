//! Cargo workspace wrapper recording the selected compiler invocation.
//!
//! The baseline contains environment hashes. Inherited values (including
//! credentials) are not copied into the record; only Cargo's changes are saved.
use serde_json::json;
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, env, fs, process::Command};

const CONTROL_ENV: [&str; 3] = [
    "LYNX_RECORD_CRATE",
    "LYNX_RECORD_FILE",
    "LYNX_RECORD_BASELINE",
];

fn run() -> Result<i32, String> {
    let mut arguments = env::args().skip(1);
    let compiler = arguments.next().ok_or("missing compiler executable")?;
    let mut arguments: Vec<_> = arguments.collect();
    // Instrument workspace crates without replacing configured RUSTFLAGS.
    // These flags retain implementations for extraction without changing
    // language-level arithmetic/overflow or target configuration.
    arguments.extend([
        "-Zalways-encode-mir".to_owned(),
        "-Zmir-opt-level=0".to_owned(),
    ]);
    let selected = env::var("LYNX_RECORD_CRATE").map_err(|e| e.to_string())?;
    let crate_name = arguments
        .windows(2)
        .find(|a| a[0] == "--crate-name")
        .map(|a| &a[1]);
    if crate_name == Some(&selected) {
        let baseline: BTreeMap<String, String> = serde_json::from_slice(
            &fs::read(env::var("LYNX_RECORD_BASELINE").map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        let actual: BTreeMap<String, String> = env::vars_os()
            .filter(|(key, _)| !CONTROL_ENV.iter().any(|control| key == control))
            .map(|(key, value)| {
                Ok((
                    key.into_string().map_err(|_| "non-UTF8 environment key")?,
                    value
                        .into_string()
                        .map_err(|_| "non-UTF8 environment value")?,
                ))
            })
            .collect::<Result<_, &str>>()?;
        let changed: BTreeMap<_, _> = actual
            .iter()
            .filter(|(key, value)| {
                baseline.get(*key) != Some(&format!("{:x}", Sha256::digest(value.as_bytes())))
            })
            .collect();
        let mut removed: Vec<_> = baseline
            .keys()
            .filter(|key| !actual.contains_key(*key))
            .map(String::as_str)
            .collect();
        removed.extend(CONTROL_ENV);
        removed.sort_unstable();
        removed.dedup();
        let record = json!({"version":1, "compiler":compiler, "arguments":arguments,
            "directory":env::current_dir().map_err(|e| e.to_string())?,
            "environment":changed, "removed_environment":removed});
        fs::write(
            env::var("LYNX_RECORD_FILE").map_err(|e| e.to_string())?,
            serde_json::to_vec(&record).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
    }
    let mut command = Command::new(compiler);
    command.args(arguments);
    // Recorder paths vary per invocation and are not application compiler inputs.
    // Remove them both here and in the recorded replay environment.
    for key in CONTROL_ENV {
        command.env_remove(key);
    }
    let status = command.status().map_err(|e| e.to_string())?;
    Ok(status.code().unwrap_or(1))
}

fn main() {
    match run() {
        Ok(code) => std::process::exit(code),
        Err(error) => {
            eprintln!("cannot record Rust compiler context: {error}");
            std::process::exit(1);
        }
    }
}
