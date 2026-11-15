defmodule Lynx.Rust.CompareExchangeTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR for extracted atomic proofs")

  @tag :tmp_dir
  test "verifies strong cross-crate compare exchange and every concurrent run", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for file <- ~w(Cargo.toml Cargo.lock core analysis nif),
        do: File.cp_r!(Path.join(@fixture, file), Path.join(workspace, file))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Atomic"))
    property = Path.join(project, "Atomic/CompareProperties.lean")
    source = File.read!(Path.join(@fixture, "CompareProperties.lean"))
    File.write!(property, source)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      tools: @tools,
      execution: :runtime,
      lean_project: project,
      module_prefix: "Atomic.Compare",
      build_dir: Path.join(tmp, "build"),
      roots: ["atomic_analysis::try_set"],
      proof_modules: ["Atomic.CompareProperties"],
      required_properties:
        Enum.map(
          ~w(contract matched mismatch composed_match composed_mismatch unavailable every_interleaving every_run),
          &("Atomic.CompareProperties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract &&
               row.theorem == "Atomic.CompareProperties.composed_match"
           end)

    assert Enum.any?(result.verification.unverified_external_calls, fn row ->
             row.implementation_verified == false &&
               String.contains?(row.rust_name, "Atomic<u64,")
           end)

    refute File.exists?(Path.join(project, "Atomic/Compare/FunsExternal_Template.lean"))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "atomic-analysis", options).reports

    file = Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules])
    export = Path.join(tmp, "compare.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for invalid <- [
          source <> "\nprivate axiom uncheckedAtomic : False\n",
          source <> "\nprivate theorem unfinishedAtomic : False := by sorry\n"
        ] do
      File.write!(property, invalid)
      Lynx.Rust.Project.build!(project, ["Atomic.CompareProperties"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(property, source)
    rust = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(rust)

    File.write!(
      rust,
      String.replace(
        original,
        "compare_exchange(expected, replacement,",
        "compare_exchange(replacement, expected,"
      )
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    end

    for pair <- ["Ordering::Relaxed, Ordering::SeqCst", "Ordering::SeqCst, Ordering::Relaxed"] do
      changed = String.replace(original, "Ordering::SeqCst, Ordering::SeqCst", pair)
      assert changed != original
      File.write!(rust, changed)

      assert_raise CompileError, ~r/only Ordering::SeqCst/, fn ->
        Lynx.Rust.verify!(workspace, "atomic-analysis", options)
      end
    end

    File.write!(rust, String.replace(original, "compare_exchange(", "compare_exchange_weak("))

    assert_raise CompileError, ~r/unverified external Rust call/, fn ->
      Lynx.Rust.verify!(workspace, "atomic-analysis", options)
    end

    File.write!(rust, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "atomic-analysis", options).reports
  end
end
