defmodule Lynx.Rust.PrefixTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/Prefix.lean", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do: @moduletag(skip: "set LYNX_AENEAS_DIR and LYNX_FULL_MIR=1 for extracted prefix proofs")

  @tag :tmp_dir
  test "verifies prefix bytes and actual comparator failures across crates", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Prefix"))

    File.write!(
      Path.join(project, "Prefix/Properties.lean"),
      File.read!(@proof)
      |> String.replace("__CORE__", "experiment_analysis.experiment_core.protocol")
      |> String.replace("__ANALYSIS__", "experiment_analysis")
      |> String.replace("__HELPER__", "experiment_analysis.core.slice.Slice.starts_with")
    )

    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      tools: @tools,
      sysroot: :full_mir,
      lean_project: project,
      module_prefix: "Prefix.Extraction",
      build_dir: Path.join(tmp, "build"),
      roots: ["experiment_analysis::recognize", "experiment_analysis::checked_prefix"],
      proof_modules: ["Prefix.Properties"],
      required_properties:
        Enum.map(
          ~w(prefix_bytes marker_exact marker_payload reject_short empty_prefix composition short_circuit comparator_panic),
          &("Prefix.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok}] = result.reports
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &(&1.lean == "Aeneas.Std.core.cmp.impls.PartialEqU8.ne" and
                 &1.implementation_verified == false)
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    unrelated = Path.join(workspace, "unrelated/src/lib.rs")
    File.write!(unrelated, File.read!(unrelated) <> "\n// Unrelated implementation revision.\n")

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    export = Path.join(tmp, "prefix.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, ["Prefix.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    source = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(source)
    independent = Path.join(tmp, "independent")
    File.mkdir_p!(Path.join(independent, "Unrelated"))

    File.write!(Path.join(independent, "Unrelated/Properties.lean"), """
    module
    public import Unrelated.Extraction.Funs
    public section
    theorem Unrelated.identity (value : Aeneas.Std.I64) :
        experiment_unrelated.identity value = Aeneas.Std.RustM.ok value := by
      simp [experiment_unrelated.identity]
    """)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(independent, ".lake"))
      File.ln_s!(packages, Path.join(independent, ".lake/packages"))
    end

    independent_options = [
      tools: @tools,
      lean_project: independent,
      module_prefix: "Unrelated.Extraction",
      build_dir: Path.join(tmp, "independent-build"),
      roots: ["experiment_unrelated::identity"],
      proof_modules: ["Unrelated.Properties"],
      required_properties: ["Unrelated.identity"]
    ]

    assert [%{status: :ok}] =
             Lynx.Rust.verify!(workspace, "experiment-unrelated", independent_options).reports

    for {before, replacement} <- [
          {"input.starts_with(prefix)", "!input.starts_with(prefix)"},
          {"self.0 != 255", "self.0 != 254"},
          {"self.0 != other.0", "false"}
        ] do
      changed = String.replace(original, before, replacement)
      assert changed != original
      File.write!(source, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end

      assert [%{status: :ok, cached: true}] =
               Lynx.Rust.verify!(workspace, "experiment-unrelated", independent_options).reports

      File.write!(source, original)

      assert [%{status: :ok}] =
               Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports
    end
  end
end
