defmodule Lynx.Rust.NativeUnwindTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "assertion-unwind-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned assertion-unwind backend")

  @tag :tmp_dir
  test "checks actual local and cross-crate assertion unwind cleanup", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Runtime"))
    property = Path.join(project, "Runtime/UnwindProperties.lean")
    proof = File.read!(Path.join(@fixture, "NativeUnwind.lean"))
    File.write!(property, proof)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots:
        Enum.map(
          ~w(mutex_assert_scalar mutex_assert_release mutex_two_assertions),
          &("effects_native::" <> &1)
        ),
      execution: :runtime,
      unwind: :assertions,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Runtime.Unwind",
      proof_modules: ["Runtime.UnwindProperties"],
      required_properties:
        Enum.map(
          ~w(callee_contract callee_state local_cleanup composed_cleanup repeated_cleanup),
          &("Runtime.UnwindProperties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports
    assert %{unwind: :assertions, native_unwind_lowering: [_ | _]} = result.verification
    assert result.extraction.translation["assertion_unwind_input"] == true
    assert Enum.any?(result.verification.native_unwind_lowering, &(&1.kind == :panic_cleanup))

    assert Enum.any?(
             result.verification.native_unwind_lowering,
             &(&1.kind == :nonpanicking_drop_call)
           )

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract &&
               row.theorem == "Runtime.UnwindProperties.composed_cleanup" &&
               "Runtime.UnwindProperties.callee_contract" in row.contracts_used
           end)

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &(&1.rust_name == "core::mem::drop")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    raw = JSON.decode!(File.read!(result.extraction.llbc))

    assert %{
             "translated" => %{
               "options" => %{
                 "preset" => nil,
                 "reconstruct_asserts" => false,
                 "reconstruct_fallible_operations" => false
               }
             }
           } = raw

    bad_flags = put_in(raw, ["translated", "options", "reconstruct_asserts"], true)
    {bad_flags, _queries} = Lynx.Rust.LLBCJson.drop_query_metadata!(bad_flags)
    bad_file = Path.join(tmp, "resugared.llbc")
    File.write!(bad_file, Lynx.Rust.LLBCJson.encode_like!(bad_flags, result.extraction.llbc))

    {output, status} =
      System.cmd(
        Path.join(@tools, "aeneas"),
        ["-backend", "lean", "-assertion-unwind-input", "-dest", project, bad_file],
        stderr_to_stdout: true
      )

    assert status != 0
    assert output =~ "Invalid extraction options"

    # Cleanup can contain compiler boolean drop flags, but arbitrary effectful
    # statements must never be mistaken for administrative destruction.
    invalid = corrupt_cleanup(raw)
    refute invalid == raw

    assert_raise CompileError, ~r/unsupported assertion unwind cleanup/, fn ->
      Lynx.Rust.NativeUnwind.lower!(invalid, result.extraction.audit.first_party)
    end

    file = Lynx.Rust.Proofs.file!(result.extraction, ["Runtime.UnwindProperties"])
    export = Path.join(tmp, "unwind.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    runtime = Path.join(project, "Runtime/NativeRuntime.lean")
    runtime_source = File.read!(runtime)

    for invalid <- [
          "private axiom assumed_unwind : True",
          "private theorem unfinished_unwind : True := by sorry"
        ] do
      File.write!(runtime, runtime_source <> "\n" <> invalid <> "\n")
      Lynx.Rust.Project.build!(project, ["Runtime.UnwindProperties"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(runtime, runtime_source)

    assert_raise CompileError, ~r/native owner lifetime|structural drop erasure rejected/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", Keyword.put(options, :unwind, :reject))
    end

    assert_raise ArgumentError, ~r/requires runtime execution/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", Keyword.put(options, :execution, :pure))
    end

    File.write!(
      property,
      proof <>
        "\ntheorem wrong_cleanup : effects_native.mutex_assert_scalar 0#u64 false {} = (.error (.error (.atom \"rust_panicked\")), {}) := by rfl\n"
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Runtime.UnwindProperties"])
    end

    File.write!(property, proof)

    native = Path.join(workspace, "native/src/lib.rs")
    source = File.read!(native)

    changed =
      String.replace(
        source,
        "pub fn mutex_assert_scalar(value: u64, accepted: bool) {\n    let _mutex = Mutex::new(value);\n    assert!(accepted);",
        "pub fn mutex_assert_scalar(value: u64, accepted: bool) {\n    let _mutex = Mutex::new(value);\n    assert!(!accepted);"
      )

    refute changed == source
    File.write!(native, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end
  end

  defp corrupt_cleanup(%{"Panic" => %{"on_unwind" => cleanup} = panic} = node) do
    bad = %{"id" => -1, "kind" => %{"Assign" => [nil, nil]}}

    Map.put(
      node,
      "Panic",
      Map.put(panic, "on_unwind", Map.update!(cleanup, "statements", &[bad | &1]))
    )
  end

  defp corrupt_cleanup(map) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, corrupt_cleanup(value)} end)

  defp corrupt_cleanup(list) when is_list(list), do: Enum.map(list, &corrupt_cleanup/1)
  defp corrupt_cleanup(value), do: value
end
