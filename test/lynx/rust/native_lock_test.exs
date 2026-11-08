defmodule Lynx.Rust.NativeLockTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
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
  test "checks actual cross-crate acquisition and preserves native proof boundaries", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Runtime"))
    property = Path.join(project, "Runtime/LockProperties.lean")
    proof = File.read!(Path.join(@fixture, "NativeLock.lean"))
    File.write!(property, proof)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::mutex_acquire"],
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Runtime.Lock",
      proof_modules: ["Runtime.LockProperties"],
      required_properties:
        Enum.map(
          ~w(callee_contract acquired composed_acquisition contention_waits recursive_cutoff missing_cutoff),
          &("Runtime.LockProperties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract &&
               row.theorem == "Runtime.LockProperties.composed_acquisition" &&
               "Runtime.LockProperties.callee_contract" in row.contracts_used
           end)

    assert Enum.any?(result.verification.unverified_external_calls, fn row ->
             String.ends_with?(row.rust_name, "::lock") and row.implementation_verified == false
           end)

    refute Enum.any?(result.verification.guarantees, &(&1.kind == :nif_adapter))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    translated = result.extraction.audit.translated
    refs = result.extraction.audit.references

    lock =
      Enum.find(
        translated["fun_decls"],
        &(&1 &&
            match?(%{native_guard_type: _}, Lynx.Rust.LockModels.resolve(&1, translated, refs)))
      )

    assert lock

    for invalid <- [
          put_in(lock, ["signature", "is_unsafe"], true),
          put_in(lock, ["signature", "abi"], "C"),
          put_in(lock, ["generics", "regions"], []),
          put_in(lock, ["signature", "output"], lock["signature"]["inputs"] |> hd()),
          put_in(lock, ["item_meta", "name"], [%{"Ident" => ["shadow_lock", 0]}])
        ],
        do: assert(is_nil(Lynx.Rust.LockModels.resolve(invalid, translated, refs)))

    model = Lynx.Rust.LockModels.resolve(lock, translated, refs)

    for id <- [model.native_guard_type, model.native_poison_type] do
      invalid =
        update_in(translated, ["type_decls"], fn types ->
          Enum.map(types, fn type ->
            if type && type["def_id"] == id,
              do: put_in(type, ["generics", "types"], []),
              else: type
          end)
        end)

      assert is_nil(Lynx.Rust.LockModels.resolve(lock, invalid, refs))
    end

    file = Lynx.Rust.Proofs.file!(result.extraction, ["Runtime.LockProperties"])
    export = Path.join(tmp, "lock.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    runtime = Path.join(project, "Runtime/NativeRuntime.lean")
    runtime_source = File.read!(runtime)

    for invalid <- [
          "private axiom assumed_lock : True",
          "private theorem unfinished_lock : True := by sorry"
        ] do
      File.write!(runtime, runtime_source <> "\n" <> invalid <> "\n")
      Lynx.Rust.Project.build!(project, ["Runtime.LockProperties"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(runtime, runtime_source)

    assert_raise CompileError, ~r/unverified external Rust call std::sync::poison::mutex/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", Keyword.put(options, :execution, :pure))
    end

    assert_raise CompileError, ~r/unverified external Rust call core::result/, fn ->
      Lynx.Rust.verify!(
        workspace,
        "effects-native",
        Keyword.put(options, :roots, ["effects_native::mutex_guarded_increment"])
      )
    end

    assert_raise CompileError, ~r/structural drop erasure rejected|native owner lifetime/, fn ->
      Lynx.Rust.verify!(
        workspace,
        "effects-native",
        Keyword.put(options, :roots, ["effects_native::mutex_acquire_and_drop"])
      )
    end

    File.write!(
      property,
      proof <>
        "\ntheorem wrong_missing : effects_native.mutex_acquire ⟨1⟩ {} = (.ok (.Ok { mutex := ⟨1⟩, token := 1, ownerContext := [], value := ⟨0#u64⟩ }), {}) := by rfl\n"
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Runtime.LockProperties"])
    end

    File.write!(property, proof)

    core = Path.join(workspace, "core/src/lib.rs")
    source = File.read!(core)

    changed =
      String.replace(
        source,
        "    mutex.lock()\n}",
        """
            match mutex.try_lock() {
                Ok(guard) => Ok(guard),
                Err(std::sync::TryLockError::Poisoned(error)) => Err(error),
                Err(std::sync::TryLockError::WouldBlock) => panic!("unexpected contention"),
            }
        }
        """,
        global: false
      )

    refute changed == source
    File.write!(core, changed)

    assert_raise ArgumentError, ~r/Charon reported extraction errors.*opaque enum/s, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end
  end
end
