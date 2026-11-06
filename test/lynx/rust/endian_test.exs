defmodule Lynx.Rust.EndianTest do
  use ExUnit.Case

  @tools System.get_env("LYNX_AENEAS_DIR")
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/Endian.lean", __DIR__)
  @moduletag timeout: 900_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for Rust endian proofs")

  @tag tmp_dir: "process-#{System.pid()}"
  test "proves endian roundtrips, cross-crate composition and safe protocol headers", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@workspace, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Endian"))
    properties = Path.join(project, "Endian/Properties.lean")
    File.cp!(@proof, properties)
    packages = Path.join(@workspace, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["experiment_analysis::endian_roundtrip", "experiment_analysis::read_header"],
      lean_project: project,
      module_prefix: "Endian.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Endian.Properties"],
      required_properties:
        Enum.map(
          ~w(little_roundtrip big_roundtrip composition short_header header_value network_order),
          &("Endian.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(
             result.verification.guarantees,
             &(&1.kind == :cross_crate_contract and &1.theorem == "Endian.Properties.composition")
           )

    models =
      Enum.filter(
        result.verification.unverified_external_calls,
        &String.contains?(&1.rust_name, "_bytes")
      )

    assert length(models) == 4
    assert Enum.all?(models, &(&1.implementation_verified == false))

    repeated = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok, cached: true}] = repeated.reports

    file = Lynx.Rust.Proofs.file!(result.extraction, ["Endian.Properties"])
    export = Path.join(tmp, "endian.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    correct = File.read!(properties)
    File.write!(properties, String.replace(correct, "some 305419896#u32", "some 1#u32"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(properties, correct)

    source = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(source)

    changed =
      String.replace(
        original,
        "u32::from_le_bytes(value.to_le_bytes())",
        "u32::from_be_bytes(value.to_le_bytes())"
      )

    assert changed != original
    File.write!(source, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end

    assert Exception.message(error) =~ "Endian/Properties.lean"
  end
end
