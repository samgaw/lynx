defmodule Lynx.Rust.NativeDropTest do
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
  test "compiler and explicit drops consume actual native cells without erasing cleanup", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for file <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, file), Path.join(workspace, file))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Runtime"))
    property = Path.join(project, "Runtime/NativeDropProperties.lean")
    proof_source = File.read!(Path.join(@fixture, "NativeDrop.lean"))
    File.write!(property, proof_source)
    packages = Path.expand("../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    roots =
      Enum.map(
        ~w(mutex_consume_scalar mutex_scope_scalar mutex_scope_flag mutex_discard_scalar mutex_checked_discard mutex_dispose_then_assert),
        &("effects_native::" <> &1)
      )

    options = [
      roots: roots,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Runtime.NativeDrop",
      proof_modules: ["Runtime.NativeDropProperties"],
      required_properties:
        Enum.map(
          ~w(increment_spec explicit_dispose scope_dispose scope_result checked_dispose dispose_before_assert consume_owned),
          &("Runtime.NativeDropProperties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports
    assert length(result.verification.native_drop_lowering) == 4

    assert Enum.any?(
             result.verification.trusted_boundary,
             &String.contains?(&1, "consuming-drop lowering")
           )

    assert Enum.any?(result.verification.unverified_external_calls, fn row ->
             row.rust_name == "core::mem::drop" && row.implementation_verified == false
           end)

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract &&
               row.theorem == "Runtime.NativeDropProperties.checked_dispose" &&
               "Runtime.NativeDropProperties.increment_spec" in row.contracts_used
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    original = JSON.decode!(File.read!(result.extraction.llbc))

    lowered =
      JSON.decode!(File.read!(Path.rootname(result.extraction.llbc) <> ".native-drops.llbc"))

    assert %{"translated" => %{"fun_decls" => functions}} = lowered
    refute functions == original["translated"]["fun_decls"]
    assert functions == result.extraction.audit.translated["fun_decls"]

    # Assertion reconstruction can omit unwind cleanup. Track
    # logical ownership even after a move into a tuple, and reject lost owners.
    consumer =
      Enum.find(functions, fn function ->
        function &&
          List.last(function["item_meta"]["name"]) ==
            %{"Ident" => ["mutex_consume_scalar", 0]}
      end)

    locals = consumer["body"]["Structured"]["locals"]["locals"]
    owner = Enum.find(locals, &(&1["index"] == 1))
    index = length(locals)
    place = %{"kind" => %{"Local" => 1}, "ty" => owner["ty"]}
    destination = %{"kind" => %{"Local" => index}}

    tuple = %{
      "Adt" => %{
        "id" => 0,
        "builtin" => "Tuple",
        "generics" => %{
          "regions" => [],
          "types" => [owner["ty"]],
          "const_generics" => [],
          "trait_refs" => []
        }
      }
    }

    for statements <- [
          [%{"kind" => %{"StorageDead" => 1}}],
          [
            %{
              "kind" => %{
                "Assign" => [destination, %{"Aggregate" => [nil, [%{"Move" => place}]]}]
              }
            },
            %{"kind" => %{"Assert" => %{}}}
          ]
        ] do
      altered =
        consumer
        |> put_in(
          ["body", "Structured", "locals", "locals"],
          locals ++ [%{"index" => index, "ty" => tuple}]
        )
        |> put_in(["body", "Structured", "body", "statements"], statements)

      assert_raise CompileError, ~r/native owner lifetime/, fn ->
        Lynx.Rust.NativeLifetimes.audit!(
          [altered],
          result.extraction.audit.external_calls,
          result.extraction.audit.translated,
          result.extraction.audit.references
        )
      end
    end

    # The kernel replay and full-module audit include both the consuming model
    # and the implementations produced by the audited instruction lowering.
    file = Lynx.Rust.Proofs.file!(result.extraction, ["Runtime.NativeDropProperties"])
    export = Path.join(tmp, "native-drop.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    runtime = Path.join(project, "Runtime/NativeRuntime.lean")
    runtime_source = File.read!(runtime)

    for invalid <- [
          "private axiom assumed_cleanup : True",
          "private theorem unfinished_cleanup : True := by sorry"
        ] do
      File.write!(runtime, runtime_source <> "\n" <> invalid <> "\n")
      Lynx.Rust.Project.build!(project, ["Runtime.NativeDropProperties"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(runtime, runtime_source)

    # A real custom destructor panics; no field codec or assumed contract may
    # replace its behavior with native cell removal.
    for root <- ~w(mutex_discard_custom) do
      assert_raise CompileError, ~r/native destruction requires/, fn ->
        Lynx.Rust.verify!(
          workspace,
          "effects-native",
          Keyword.put(options, :roots, ["effects_native::" <> root])
        )
      end
    end

    for root <- ~w(mutex_assert_scalar) do
      assert_raise CompileError, ~r/structural drop erasure rejected|native owner lifetime/, fn ->
        Lynx.Rust.verify!(
          workspace,
          "effects-native",
          Keyword.put(options, :roots, ["effects_native::" <> root])
        )
      end
    end

    # Mutating a compiler dictionary cannot redirect destruction to another
    # implementation, even if its names and value representation look similar.
    drop_id =
      Enum.find_value(result.extraction.audit.external_calls, fn {id, model} ->
        if model[:native_dispose], do: id
      end)

    invalid =
      update_in(lowered, ["translated", "trait_impls"], fn impls ->
        Enum.map(impls, fn impl ->
          if impl && impl["src"] == "Destruct" &&
               Enum.any?(impl["item_meta"]["name"], &(&1 == %{"Ident" => ["Mutex", 0]})),
             do:
               update_in(impl, ["methods"], fn [method] ->
                 [put_in(method, ["skip_binder", "id"], drop_id)]
               end),
             else: impl
        end)
      end)

    assert_raise CompileError, ~r/native destruction requires/, fn ->
      Lynx.Rust.LLBC.audit!(invalid, result.extraction.audit.first_party, execution: :runtime)
    end

    File.write!(
      property,
      proof_source <>
        "\n theorem wrong_release : effects_native.mutex_scope_scalar 7#u64 {} = (.ok (), {}) := by rfl\n"
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Runtime.NativeDropProperties"])
    end

    File.write!(property, proof_source)
    rust = Path.join(workspace, "native/src/lib.rs")
    source = File.read!(rust)
    changed = Regex.replace(~r/(pub fn mutex_scope_flag\([^}]+)true\n}/, source, "\\1false\n}")
    refute changed == source
    File.write!(rust, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    # This root has no constructor or existing call statement. Auto-discovery
    # must still supply the real consuming declaration and serialize its call.
    [_, consume] = String.split(proof_source, "theorem consume_owned", parts: 2)

    File.write!(Path.join(project, "Runtime/OwnedDropProperties.lean"), """
    module
    public import Runtime.OwnedDrop.Funs
    public section
    open Aeneas Aeneas.Std Lynx effects_native
    namespace Runtime.NativeDropProperties
    theorem consume_owned#{consume}
    """)

    owned =
      options
      |> Keyword.put(:roots, ["effects_native::mutex_consume_scalar"])
      |> Keyword.put(:module_prefix, "Runtime.OwnedDrop")
      |> Keyword.put(:proof_modules, ["Runtime.OwnedDropProperties"])
      |> Keyword.put(:required_properties, ["Runtime.NativeDropProperties.consume_owned"])

    assert %{reports: [%{status: :ok}], verification: %{native_drop_lowering: [_]}} =
             Lynx.Rust.verify!(workspace, "effects-native", owned)
  end
end
