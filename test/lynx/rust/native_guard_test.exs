defmodule Lynx.Rust.NativeGuardTest do
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
  test "verifies borrowed guard updates across crates without accepting failure-state loss", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Runtime"))
    property = Path.join(project, "Runtime/GuardProperties.lean")
    proof = File.read!(Path.join(@fixture, "NativeGuard.lean"))
    File.write!(property, proof)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::guard_read", "effects_native::guard_increment"],
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Runtime.Guard",
      proof_modules: ["Runtime.GuardProperties"],
      required_properties:
        Enum.map(
          ~w(increment_spec callee_contract composed_update read_payload update_spec update_environment),
          &("Runtime.GuardProperties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert [%{rust: "std::sync::poison::mutex::MutexGuard", lean: "Lynx.NativeGuard"}] =
             result.extraction.audit.external_types

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract &&
               row.theorem == "Runtime.GuardProperties.composed_update" &&
               "Runtime.GuardProperties.callee_contract" in row.contracts_used
           end)

    refute Enum.any?(result.verification.guarantees, &(&1.kind == :nif_adapter))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    translated = result.extraction.audit.translated
    refs = result.extraction.audit.references

    # A transitive implementation can fail even when the guard-taking wrapper
    # contains no assertion. Never infer safety solely from the wrapper body.
    functions = result.extraction.audit.functions

    callee =
      Enum.find(
        functions,
        &(&1["item_meta"]["name"] == [
            %{"Ident" => ["effects_core", 0]},
            %{"Ident" => ["increment", 0]}
          ])
      )

    assert callee

    for failing <- [
          %{"Panic" => %{"on_unwind" => %{"statements" => []}}},
          %{"Loop" => %{"statements" => []}}
        ] do
      invalid =
        Enum.map(functions, fn function ->
          if function["def_id"] == callee["def_id"] do
            put_in(function, ["body", "Structured", "body", "statements"], [%{"kind" => failing}])
          else
            function
          end
        end)

      # The checker reads compiler declarations to retain complete constant
      # tables. Change that authoritative body as well as the selected audit copy.
      callee_id = callee["def_id"]
      changed = Enum.find(invalid, &(&1["def_id"] == callee["def_id"]))

      invalid_translated =
        Map.update!(translated, "fun_decls", fn declarations ->
          Enum.map(declarations, fn
            %{"def_id" => id} when id == callee_id -> changed
            declaration -> declaration
          end)
        end)

      assert_raise CompileError, ~r/borrowed native guard requires nonpanicking/, fn ->
        Lynx.Rust.NativeBorrows.audit!(
          invalid,
          result.extraction.audit.external_calls,
          invalid_translated,
          refs
        )
      end
    end

    views =
      Enum.filter(
        translated["fun_decls"],
        &(&1 && Lynx.Rust.GuardModels.resolve(&1, translated, refs))
      )

    assert length(views) == 2

    for view <- views do
      for invalid <- [
            put_in(view, ["signature", "abi"], "C"),
            put_in(view, ["signature", "is_unsafe"], true),
            put_in(view, ["generics", "regions"], []),
            put_in(view, ["src", "TraitImpl", "reuses_default"], true),
            put_in(view, ["signature", "output"], view["signature"]["inputs"] |> hd())
          ],
          do: assert(is_nil(Lynx.Rust.GuardModels.resolve(invalid, translated, refs)))

      impl_id = get_in(view, ["src", "TraitImpl", "impl_ref", "id"])

      invalid =
        update_in(translated, ["trait_impls"], fn impls ->
          Enum.map(impls, fn impl ->
            if impl && impl["def_id"] == impl_id, do: Map.put(impl, "methods", []), else: impl
          end)
        end)

      assert is_nil(Lynx.Rust.GuardModels.resolve(view, invalid, refs))
    end

    file = Lynx.Rust.Proofs.file!(result.extraction, ["Runtime.GuardProperties"])
    export = Path.join(tmp, "guard.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for root <- ~w(guard_increment_then_assert guard_envelope_then_assert) do
      assert_raise CompileError, ~r/borrowed native guard requires nonpanicking/, fn ->
        Lynx.Rust.verify!(
          workspace,
          "effects-native",
          Keyword.put(options, :roots, ["effects_native::" <> root])
        )
      end
    end

    assert_raise CompileError, ~r/unverified external Rust call/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", Keyword.put(options, :execution, :pure))
    end

    File.write!(
      property,
      proof <>
        "\ntheorem wrong_read (guard : Lynx.NativeGuard effects_core.Counter) : effects_native.guard_read guard = Lynx.Result.ok 0#u64 := by rfl\n"
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Runtime.GuardProperties"])
    end

    File.write!(property, proof)
    core = Path.join(workspace, "core/src/lib.rs")
    source = File.read!(core)
    changed = String.replace(source, "    increment(guard, amount)", "    increment(guard, 0)")
    refute source == changed
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end
  end
end
