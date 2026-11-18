//! Checks that nested-root selection preserves upstream re-export resolution.

use assert_cmd::prelude::OutputAssertExt;
use charon_lib::{export::CrateData, options::SerializationFormat};
use std::{fs, process::Command};

#[test]
fn selecting_a_dependency_reexport_preserves_its_compiler_definition() -> anyhow::Result<()> {
    let temp = tempfile::tempdir()?;
    let path = temp.path();
    let dependency = path.join("dependency.rs");
    let library = path.join("libalias_dependency.rlib");
    let source = path.join("root.rs");
    let output = path.join("alias.llbc");

    fs::write(
        &dependency,
        r#"
pub fn selected(value: bool) -> bool { !value }

pub mod exports {
    pub use crate::selected as first;
    pub use crate::selected as second;
}
"#,
    )?;
    fs::write(&source, "extern crate alias_dependency;")?;

    Command::new("rustc")
        .args([
            "-Zalways-encode-mir",
            "--crate-name",
            "alias_dependency",
            "--crate-type",
            "rlib",
        ])
        .arg(&dependency)
        .arg("-o")
        .arg(&library)
        .assert()
        .try_success()?;

    Command::new(env!("CARGO_BIN_EXE_charon"))
        .args([
            "rustc",
            "--sysroot",
            "default",
            "--start-from",
            "alias_dependency::exports::second",
            "--include",
            "alias_dependency",
            "--dest-file",
        ])
        .arg(&output)
        .args(["--", "--crate-name", "alias_root", "--crate-type", "lib"])
        .arg(&source)
        .arg("--extern")
        .arg(format!("alias_dependency={}", library.display()))
        .assert()
        .try_success()?;

    let crate_data = CrateData::deserialize_from_file(&output, SerializationFormat::Json)?;
    let data = &crate_data.translated;
    assert!(data.fun_decls.iter().any(|decl| {
        decl.item_meta.name.debug_repr(data) == "alias_dependency::selected"
            && decl.item_meta.started_from
            && decl.body.as_structured().is_some()
    }));
    Ok(())
}
