defmodule Lynx.Rust.IndexedSlicesTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/Indexed.lean", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for indexed slice proofs")

  @tag :tmp_dir
  test "proves indexed bytes, exact consumption and panics across crates", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Indexed"))

    File.write!(
      Path.join(project, "Indexed/Properties.lean"),
      File.read!(@proof)
      |> String.replace("__CORE__", "experiment_analysis.experiment_core")
      |> String.replace("__ANALYSIS__", "experiment_analysis")
    )

    File.write!(
      Path.join(project, "Indexed/WindowProperties.lean"),
      File.read!(Path.join(Path.dirname(@proof), "IndexedWindow.lean"))
      |> String.replace("__CORE__", "experiment_analysis.experiment_core")
      |> String.replace("__ANALYSIS__", "experiment_analysis")
    )

    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      tools: @tools,
      lean_project: project,
      module_prefix: "Indexed.Extraction",
      build_dir: Path.join(tmp, "build"),
      roots: [
        "experiment_analysis::indexed_window",
        "experiment_analysis::indexed_split",
        "experiment_analysis::array_window_length"
      ],
      proof_modules: ["Indexed.WindowProperties", "Indexed.Properties"],
      required_properties:
        Enum.map(
          ~w(core_window core_prefix window_bytes exact_consumption split_panics array_success array_panics),
          &("Indexed.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok}] = result.reports

    for kind <- ~w(Range RangeTo) do
      assert Enum.any?(
               result.verification.unverified_external_calls,
               &(&1.lean == "Aeneas.Std.core.slice.index.SliceIndex#{kind}UsizeSlice.index" and
                   &1.status == :modelled and &1.implementation_verified == false)
             )
    end

    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    export = Path.join(tmp, "indexed.export")

    file =
      Lynx.Rust.Proofs.file!(result.extraction, ["Indexed.WindowProperties", "Indexed.Properties"])

    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    source = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(source)

    for {before, after_text} <- [
          {"&input[start..end]", "&input[..end]"},
          {"&input[..end]", "&input[1..end]"}
        ] do
      changed = String.replace(original, before, after_text)
      assert changed != original
      File.write!(source, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end

      File.write!(source, original)

      assert [%{status: :ok}] =
               Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports
    end

    for function <- ~w(indexed_remainder indexed_array_remainder indexed_vector_remainder) do
      assert_raise CompileError, ~r/missing or unsupported SliceIndex/, fn ->
        Lynx.Rust.verify!(workspace, "experiment-core",
          tools: @tools,
          lean_project: project,
          module_prefix: "Indexed.Unsupported",
          build_dir: Path.join(tmp, "unsupported-build"),
          roots: ["experiment_core::protocol::" <> function]
        )
      end
    end
  end
end
