defmodule Lynx.Rust.RuntimeTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @runtime_backend "aeneas=nightly-2026.11.04-2b9e3ea+lynx-result-monad-v1"
  @moduletag timeout: 600_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), @runtime_backend)
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned result-monad backend")

  @tag :tmp_dir
  test "composes actual extracted computations with runtime effects and audits their proofs", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for file <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, file), Path.join(workspace, file))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Runtime"))
    proof = Path.join(project, "Runtime/Properties.lean")
    source = File.read!(Path.join(@fixture, "Runtime.lean"))
    File.write!(proof, source)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: [
        "effects_native::increment_twice",
        "effects_native::require_nonzero",
        "effects_native::checked_next"
      ],
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Runtime.Extraction",
      proof_modules: ["Runtime.Properties"],
      required_properties:
        Enum.map(
          ~w(increment_spec twice_success twice_second_overflow nonzero_success zero_panics checked_next_success checked_next_overflow state_before_panic),
          &("Runtime.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports
    assert result.verification.execution == :runtime
    assert result.extraction.translation["result_monad"] == "Lynx.NativeM"

    assert Enum.any?(result.verification.guarantees, fn property ->
             property.kind == :cross_crate_contract &&
               property.theorem == "Runtime.Properties.twice_success" &&
               "Runtime.Properties.increment_spec" in property.contracts_used
           end)

    assert Enum.any?(result.verification.external_models, &String.contains?(&1, "rust_panicked"))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    assert_raise ArgumentError, ~r/result monad/, fn ->
      Lynx.Rust.LLBC.link!(result.extraction.audit, result.extraction.translation)
    end

    # The checked runtime and every generated implementation are replayed using
    # the same independent export checker as ordinary Lynx laws.
    file = Lynx.Rust.Proofs.file!(result.extraction, ["Runtime.Properties"])
    export = Path.join(tmp, "runtime.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for unfinished <- [
          "private axiom unchecked : True",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(proof, source <> "\n" <> unfinished <> "\n")
      Lynx.Rust.Project.build!(project, ["Runtime.Properties"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(proof, source)
    rust = Path.join(workspace, "core/src/lib.rs")

    File.write!(
      rust,
      String.replace(File.read!(rust), "counter.value = value;", "counter.value = amount;")
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end
  end

  @tag :tmp_dir
  test "validates the backend selector and preserves user runtime modules", %{tmp_dir: tmp} do
    for selector <- ["Lynx..NativeM", "Lynx.NativeM;axiom", "", "Lynx.NativeM\n"] do
      {output, status} =
        System.cmd(Path.join(@tools, "aeneas"), ["-lean-result-monad", selector],
          stderr_to_stdout: true
        )

      assert status != 0
      assert output =~ "dotted Lean identifier"
    end

    {output, status} =
      System.cmd(
        Path.join(@tools, "aeneas"),
        ["-backend", "coq", "-lean-result-monad", "Lynx.NativeM"],
        stderr_to_stdout: true
      )

    assert status != 0
    assert output =~ "requires -backend lean"

    File.mkdir_p!(Path.join(tmp, "Runtime"))
    path = Path.join(tmp, "Runtime/NativeRuntime.lean")
    File.write!(path, "-- user module\n")

    assert_raise ArgumentError, ~r/refusing to overwrite/, fn ->
      Lynx.Rust.Runtime.configuration!(:runtime, tmp, "Runtime.Extraction")
    end

    assert File.read!(path) == "-- user module\n"
  end
end
