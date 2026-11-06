defmodule Lynx.Rust.NativeCriticalTest do
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
  test "verifies full cross-crate critical sections and poisoned ownership recovery", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Runtime"))
    property = Path.join(project, "Runtime/CriticalProperties.lean")
    proof = File.read!(Path.join(@fixture, "NativeCritical.lean"))
    File.write!(property, proof)
    concurrent = Path.join(project, "Runtime/CriticalConcurrent.lean")
    concurrent_proof = File.read!(Path.join(@fixture, "NativeCriticalConcurrent.lean"))
    File.write!(concurrent, concurrent_proof)
    modules = ["Runtime.CriticalProperties", "Runtime.CriticalConcurrent"]
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::locked_increment"],
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Runtime.Critical",
      proof_modules: modules,
      required_properties:
        Enum.map(
          ~w(increment_spec callee_contract release_contract recover_success recover_poisoned critical_contract critical_state contention_waits missing_cutoff),
          &("Runtime.CriticalProperties." <> &1)
        ) ++
          Enum.map(
            ~w(updates_interleave updates_interleave_child_first),
            &("Runtime.CriticalConcurrent." <> &1)
          )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract &&
               row.theorem == "Runtime.CriticalProperties.critical_contract" &&
               "Runtime.CriticalProperties.release_contract" in row.contracts_used
           end)

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &(String.ends_with?(&1.rust_name, "::into_inner") &&
                 &1.implementation_verified == false)
           )

    refute Enum.any?(result.verification.guarantees, &(&1.kind == :nif_adapter))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    audit = result.extraction.audit

    into_inner =
      Enum.find(
        audit.translated["fun_decls"],
        &(&1 && Lynx.Rust.PoisonModels.resolve(&1, audit.translated, audit.references))
      )

    assert into_inner

    for invalid <- [
          put_in(into_inner, ["signature", "abi"], "C"),
          put_in(into_inner, ["signature", "is_unsafe"], true),
          put_in(into_inner, ["signature", "output"], hd(into_inner["signature"]["inputs"])),
          put_in(into_inner, ["generics", "types"], [])
        ],
        do:
          assert(
            is_nil(Lynx.Rust.PoisonModels.resolve(invalid, audit.translated, audit.references))
          )

    no_transfer =
      update_in(
        audit.external_calls,
        [into_inner["def_id"]],
        &Map.put(&1, :native_transfer, false)
      )

    assert_raise CompileError, ~r/native owner lifetime/, fn ->
      Lynx.Rust.NativeLifetimes.audit!(
        audit.functions,
        no_transfer,
        audit.translated,
        audit.references
      )
    end

    for change <- [:copy, :branch, :fallthrough] do
      invalid =
        Enum.map(audit.functions, fn function ->
          if String.contains?(inspect(function["item_meta"]["name"]), "recover_guard"),
            do: Map.update!(function, "body", &alter_ownership(&1, change)),
            else: function
        end)

      refute invalid == audit.functions

      assert_raise CompileError, ~r/native owner lifetime/, fn ->
        Lynx.Rust.NativeLifetimes.audit!(
          invalid,
          audit.external_calls,
          audit.translated,
          audit.references
        )
      end
    end

    result_type =
      Enum.find(audit.translated["type_decls"], fn type ->
        type &&
          Lynx.Rust.LLBC.result_type?(type["def_id"], %{
            translated: audit.translated,
            references: audit.references
          })
      end)

    invalid =
      update_in(audit.translated, ["type_decls"], fn types ->
        Enum.map(types, fn type ->
          if type && type["def_id"] == result_type["def_id"] do
            update_in(
              type,
              ["kind", "Enum"],
              &Enum.map(&1, fn variant ->
                Map.update!(variant, "fields", fn fields -> fields ++ fields end)
              end)
            )
          else
            type
          end
        end)
      end)

    assert_raise CompileError, ~r/native owner lifetime/, fn ->
      Lynx.Rust.NativeLifetimes.audit!(
        audit.functions,
        audit.external_calls,
        invalid,
        audit.references
      )
    end

    file = Lynx.Rust.Proofs.file!(result.extraction, modules)
    export = Path.join(tmp, "critical.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for theorem <- ~w(updates_interleave updates_interleave_child_first) do
      assert Enum.any?(
               result.verification.guarantees,
               &(&1.theorem == "Runtime.CriticalConcurrent." <> theorem)
             )
    end

    # Keep the arithmetic assumptions and actual implementation intact while
    # claiming that the original value survives both positive updates.
    wrong_concurrent =
      String.replace(
        concurrent_proof,
        "NativeCodec.encode (effects_core.Counter.mk final)])] := by",
        "NativeCodec.encode (effects_core.Counter.mk before)])] := by"
      )

    refute wrong_concurrent == concurrent_proof
    File.write!(concurrent, wrong_concurrent)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Runtime.CriticalConcurrent"])
    end

    File.write!(concurrent, concurrent_proof)

    File.write!(
      property,
      proof <>
        "\ntheorem wrong_critical (mutex : Lynx.NativeMutex effects_core.Counter) (amount : Aeneas.Std.U64) : effects_native.locked_increment mutex amount = Lynx.Result.ok true := by rfl\n"
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Runtime.CriticalProperties"])
    end

    File.write!(property, proof)
    core = Path.join(workspace, "core/src/lib.rs")
    source = File.read!(core)

    changed =
      String.replace(source, "    update_release(guard, amount)", "    update_release(guard, 0)")

    refute source == changed
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    changed =
      String.replace(
        source,
        "Err(error) => error.into_inner(),",
        "Err(error) => { assert!(false); error.into_inner() },"
      )

    refute source == changed
    File.write!(core, changed)

    assert_raise CompileError, ~r/structural drop erasure rejected|native owner lifetime/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end
  end

  defp alter_ownership(%{"Move" => %{"kind" => %{"Projection" => _}} = place}, :copy),
    do: %{"Copy" => place}

  defp alter_ownership(%{"Switch" => switch}, :branch) do
    branches =
      Enum.map(switch["branches"], fn branch ->
        Map.update!(
          branch,
          "statements",
          &Enum.reject(&1, fn statement -> statement["kind"] == "Return" end)
        )
      end)

    %{"Switch" => %{switch | "branches" => branches}}
  end

  defp alter_ownership(%{"Structured" => body}, :fallthrough) do
    %{
      "Structured" =>
        update_in(
          body,
          ["body", "statements"],
          &Enum.reject(&1, fn statement -> statement["kind"] == "Return" end)
        )
    }
  end

  defp alter_ownership(map, change) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, alter_ownership(value, change)} end)

  defp alter_ownership(list, change) when is_list(list),
    do: Enum.map(list, &alter_ownership(&1, change))

  defp alter_ownership(value, _), do: value
end
