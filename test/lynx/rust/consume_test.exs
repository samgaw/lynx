defmodule Lynx.Rust.ConsumeTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do: @moduletag(skip: "set LYNX_AENEAS_DIR and LYNX_FULL_MIR=1 for prefix consumption proofs")

  @tag :tmp_dir
  test "proves exact remainder, pattern conversion and comparator order across crates", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Consume"))

    for {source, target} <- [
          {"Consume.lean", "Properties.lean"},
          {"ConsumeArray.lean", "ArrayProperties.lean"}
        ] do
      File.write!(
        Path.join(project, "Consume/" <> target),
        File.read!(Path.join(@proofs, source))
        |> String.replace("__ROOT__", "experiment_analysis")
        |> String.replace("__ANALYSIS__", "experiment_analysis")
        |> String.replace("__CORE__", "experiment_analysis.experiment_core.protocol")
      )
    end

    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      tools: @tools,
      sysroot: :full_mir,
      lean_project: project,
      module_prefix: "Consume.Extraction",
      build_dir: Path.join(tmp, "build"),
      roots:
        Enum.map(
          ~w(consume_marker consume_array_marker consumed_length checked_consume checked_recognize),
          &("experiment_analysis::" <> &1)
        ),
      proof_modules: ["Consume.Properties", "Consume.ArrayProperties"],
      required_properties:
        Enum.map(
          ~w(consume_bytes conservation marker_bytes array_bytes length_bytes empty_prefix comparator_panic recognize_without_panic),
          &("Consume.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok}] = result.reports
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &(&1.lean == "Aeneas.Std.core.slice.Slice.split_at" and
                 &1.implementation_verified == false)
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    export = Path.join(tmp, "consume.export")

    file =
      Lynx.Rust.Proofs.file!(result.extraction, ["Consume.Properties", "Consume.ArrayProperties"])

    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    unrelated = Path.join(workspace, "unrelated/src/lib.rs")
    File.write!(unrelated, File.read!(unrelated) <> "\n// Independent revision.\n")

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    source = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(source)

    for {before, replacement} <- [
          {"input.strip_prefix(prefix)",
           "match input.strip_prefix(prefix) { Some(_) => Some(input), None => None }"},
          {"input.strip_prefix(b\"LYNX\")", "input.strip_prefix(b\"LYNY\")"},
          {"input.strip_prefix(&prefix)", "prefix.strip_prefix(&input)"},
          {"self.0 != 255", "self.0 != 254"}
        ] do
      changed = String.replace(original, before, replacement)
      assert changed != original
      File.write!(source, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end

      File.write!(source, original)

      assert [%{status: :ok}] =
               Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports
    end
  end
end
