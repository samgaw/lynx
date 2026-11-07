defmodule Lynx.Rust.FileIoTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_io", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "verifies cross-crate write synchronization and rejects changed implementations", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock rust-toolchain.toml core protocol),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Disk"))
    property = Path.join(project, "Disk/Properties.lean")
    original = File.read!(Path.join(@fixture, "Properties.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["io_protocol::write_then_sync"],
      execution: :runtime,
      files: :regular,
      tools: @tools,
      lean_project: project,
      module_prefix: "Disk.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Disk.Properties"],
      required_properties:
        Enum.map(
          ~w(cross_contract protocol_success protocol_write_error protocol_sync_error write_alone),
          &("Disk.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports
    assert result.verification.files == :regular

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract &&
                 &1.theorem == "Disk.Properties.protocol_success")
           )

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "filesystem/device")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "io.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom fileTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    File.write!(property, original)

    source = Path.join(workspace, "protocol/src/lib.rs")
    rust = File.read!(source)

    wrong_order = """
    use std::{fs::File, io};
    pub fn write_then_sync(file: &mut File, bytes: &[u8]) -> io::Result<usize> {
        match io_core::synchronize(file) {
            Err(error) => Err(error),
            Ok(()) => io_core::write_once(file, bytes),
        }
    }
    """

    File.write!(source, wrong_order)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", options)
    end

    File.write!(source, rust)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    assert_raise CompileError, fn ->
      Lynx.Rust.verify!(workspace, "io-protocol", Keyword.delete(options, :files))
    end
  end
end
