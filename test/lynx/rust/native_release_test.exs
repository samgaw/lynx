defmodule Lynx.Rust.NativeReleaseTest do
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
  test "checks owning guard updates, release and reacquisition against compiled implementations",
       %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Runtime"))
    property = Path.join(project, "Runtime/ReleaseProperties.lean")
    proof = File.read!(Path.join(@fixture, "NativeRelease.lean"))
    File.write!(property, proof)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots:
        Enum.map(
          ~w(guard_update_release guard_release guard_release_then_assert guard_update_reacquire guard_update_scope),
          &("effects_native::" <> &1)
        ),
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Runtime.Release",
      proof_modules: ["Runtime.ReleaseProperties"],
      required_properties:
        Enum.map(
          ~w(increment_spec callee_contract release_contract composed_release update_release_state release_state panic_after_release reacquire_contract reacquired_payload missing_cutoff context_cutoff token_cutoff scope_release_contract),
          &("Runtime.ReleaseProperties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract &&
               row.theorem == "Runtime.ReleaseProperties.composed_release" &&
               "Runtime.ReleaseProperties.release_contract" in row.contracts_used
           end)

    assert [_ | _] = result.verification.native_drop_lowering

    assert Enum.any?(
             result.verification.native_unwind_lowering,
             &(&1.kind == :nonpanicking_borrow_call)
           )

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &(&1.rust_name == "core::mem::drop" && &1.implementation_verified == false)
           )

    refute Enum.any?(result.verification.guarantees, &(&1.kind == :nif_adapter))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    audit = result.extraction.audit
    # Guard destruction derives its actual payload codec even without a new/lock root.
    only_drops = Map.filter(audit.external_calls, fn {_, model} -> model[:native_codec_drop] end)

    assert [
             %{
               "item_meta" => %{
                 "name" => [%{"Ident" => ["effects_core", 0]}, %{"Ident" => ["Counter", 0]}]
               }
             }
           ] =
             Lynx.Rust.NativeCodecs.plan!(%{audit | external_calls: only_drops})

    impl =
      Enum.find(audit.translated["trait_impls"], fn impl ->
        impl && impl["src"] == "Destruct" &&
          String.contains?(inspect(impl["item_meta"]["name"]), "MutexGuard")
      end)

    assert impl
    [method] = impl["methods"]

    for transform <- [
          fn t ->
            update_in(
              t,
              ["trait_impls"],
              &Enum.map(&1, fn row ->
                if row && row["def_id"] == impl["def_id"],
                  do: Map.put(row, "methods", []),
                  else: row
              end)
            )
          end,
          fn t ->
            update_in(
              t,
              ["fun_decls"],
              &Enum.map(&1, fn row ->
                if row && row["def_id"] == method["skip_binder"]["id"],
                  do: put_in(row, ["signature", "abi"], "C"),
                  else: row
              end)
            )
          end,
          fn t ->
            update_in(
              t,
              ["fun_decls"],
              &Enum.map(&1, fn row ->
                if row && row["def_id"] == method["skip_binder"]["id"],
                  do: put_in(row, ["generics", "regions"], []),
                  else: row
              end)
            )
          end
        ] do
      assert {:error, _, message} =
               Lynx.Rust.NativeDrops.audit(
                 audit.functions,
                 audit.external_calls,
                 transform.(audit.translated),
                 audit.references
               )

      assert message =~ "native destruction requires"
    end

    file = Lynx.Rust.Proofs.file!(result.extraction, ["Runtime.ReleaseProperties"])
    export = Path.join(tmp, "release.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for unwind <- [:reject, :assertions] do
      assert_raise CompileError,
                   ~r/structural drop erasure rejected|unsupported.*unwind|native.*cleanup|native owner lifetime/,
                   fn ->
                     Lynx.Rust.verify!(
                       workspace,
                       "effects-native",
                       options
                       |> Keyword.put(:roots, ["effects_native::guard_owned_then_assert"])
                       |> Keyword.put(:unwind, unwind)
                     )
                   end
    end

    runtime = Path.join(project, "Runtime/NativeRuntime.lean")
    source_runtime = File.read!(runtime)

    for invalid <- [
          "private axiom assumed_release : True",
          "private theorem unfinished_release : True := by sorry"
        ] do
      File.write!(runtime, source_runtime <> "\n" <> invalid <> "\n")
      Lynx.Rust.Project.build!(project, ["Runtime.ReleaseProperties"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(runtime, source_runtime)

    File.write!(
      property,
      proof <>
        "\ntheorem wrong_release (guard : Lynx.NativeGuard effects_core.Counter) (env : Lynx.Environment) : effects_native.guard_release guard env = (.ok (), env) := by rfl\n"
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Runtime.ReleaseProperties"])
    end

    File.write!(property, proof)
    core = Path.join(workspace, "core/src/lib.rs")
    source = File.read!(core)

    changed =
      String.replace(
        source,
        "    let changed = increment_guard(&mut guard, amount);",
        "    let changed = increment_guard(&mut guard, 0);"
      )

    refute source == changed
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    # A newly failing callee must retain its compiler cleanup and be rejected.
    changed =
      String.replace(
        source,
        "    increment(guard, amount)",
        "    assert!(amount != 0);\n    increment(guard, amount)"
      )

    refute source == changed
    File.write!(core, changed)

    assert_raise CompileError,
                 ~r/structural drop erasure rejected|borrowed native guard requires|native owner lifetime/,
                 fn -> Lynx.Rust.verify!(workspace, "effects-native", options) end
  end
end
