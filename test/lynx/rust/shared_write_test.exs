defmodule Lynx.Rust.SharedWriteTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "shared file writes verify through the Rust API without NIF exposure", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "SharedWrite"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    property = Path.join(project, "SharedWrite/Properties.lean")
    source = File.read!(Path.join(@fixture, "NativeSharedWrite.lean"))
    File.write!(property, source)

    options = [
      roots: ["effects_native::file_resource_write"],
      execution: :runtime,
      files: :regular,
      owned_drops: true,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "SharedWrite.Extraction",
      proof_modules: ["SharedWrite.Properties"],
      required_properties:
        ~w(SharedWrite.Properties.cross_contract SharedWrite.Properties.write_next)
    ]

    checked = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = checked.reports

    assert Enum.any?(
             checked.verification.guarantees,
             &match?(%{kind: :cross_crate_contract, status: :verified}, &1)
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    File.write!(property, String.replace(source, "next reply", "next (.Ok 0#usize)"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    File.write!(property, source)
    core = Path.join(workspace, "core/src/lib.rs")
    rust = File.read!(core)

    changed =
      String.replace(
        rust,
        "    borrowed.write(bytes)",
        "    let _ = borrowed;\n    let _ = bytes;\n    Ok(0)"
      )

    assert changed != rust
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end
  end
end
