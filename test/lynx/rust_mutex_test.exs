defmodule Lynx.Rust.MutexTest do
  use ExUnit.Case
  @fixture Path.expand("../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "lynx-result-monad-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned result-monad backend")

  @tag :tmp_dir
  test "proves the actual cross-crate mutex factory and preserves native proof audits", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for file <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, file), Path.join(workspace, file))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Runtime"))

    File.cp!(
      Path.join(@fixture, "Mutex.lean"),
      Path.join(project, "Runtime/MutexProperties.lean")
    )

    packages = Path.expand("../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: [
        "effects_native::mutex_new_incremented",
        "effects_native::mutex_snapshot",
        "effects_native::mutex_pair"
      ],
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Runtime.Mutex",
      proof_modules: ["Runtime.MutexProperties"],
      required_properties:
        Enum.map(
          ~w(increment_spec initialized initialized_readback collision_exhausts snapshot_initialized paired_identities),
          &("Runtime.MutexProperties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract &&
               row.theorem == "Runtime.MutexProperties.initialized" &&
               "Runtime.MutexProperties.increment_spec" in row.contracts_used
           end)

    assert Enum.any?(result.verification.unverified_external_calls, fn row ->
             row.implementation_verified == false && String.contains?(row.rust_name, "Mutex")
           end)

    refute Enum.any?(result.verification.guarantees, &(&1.kind == :nif_adapter))
    codecs = "Runtime.Mutex.NativeCodecs"
    assert codecs in result.extraction.model_modules

    file = Lynx.Rust.Proofs.file!(result.extraction, ["Runtime.MutexProperties"])
    export = Path.join(tmp, "mutex.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    generated = Path.join(project, "Runtime/Mutex/NativeCodecs.lean")
    source = File.read!(generated)

    for invalid <- [
          "private axiom unchecked_heap : True",
          "private theorem unfinished_heap : True := by sorry"
        ] do
      File.write!(generated, source <> "\n" <> invalid <> "\n")
      Lynx.Rust.Project.build!(project, [codecs])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(generated, source)

    assert_raise CompileError, ~r/unverified external Rust call std::sync::poison::mutex/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", Keyword.put(options, :execution, :pure))
    end

    for root <- ["effects_native::mutex_generic", "effects_native::mutex_borrowed"] do
      assert_raise ArgumentError, ~r/unsupported native heap payload/, fn ->
        Lynx.Rust.verify!(workspace, "effects-native", Keyword.put(options, :roots, [root]))
      end
    end

    rust = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      rust,
      String.replace(
        File.read!(rust),
        "let mut counter = effects_core::Counter { value };",
        "let mut counter = effects_core::Counter { value: amount };"
      )
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end
  end
end
