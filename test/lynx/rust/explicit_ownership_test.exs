defmodule Lynx.Rust.ExplicitOwnershipTest do
  use ExUnit.Case
  alias Lynx.Rust.{ExplicitOwnership, LLBCJson}

  @fixture Path.expand("../../fixtures/rust/explicit_ownership.json", __DIR__)
  @workspace Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR")

  test "no-op instances retain compiler self identities and do not replace source bodies" do
    doc = @fixture |> File.read!() |> JSON.decode!()
    adapted = ExplicitOwnership.prepare!(doc)
    assert length(adapted.primitive_models) == 3
    assert Enum.all?(adapted.primitive_models, &(&1.implementation_verified == false))
    source = doc["translated"]
    target = adapted.document["translated"]
    assert length(target["fun_decls"]) == length(source["fun_decls"]) + 1

    for {before, after_} <- Enum.zip(source["fun_decls"], target["fun_decls"]) do
      impls = Enum.map(adapted.primitive_models, & &1.implementation_id)
      assert erase_witness(before, impls) == erase_witness(after_, impls)
    end

    assert %{
             "signature" => %{"is_unsafe" => true, "abi" => "Rust"},
             "body" => %{"Structured" => %{"locals" => %{"arg_count" => 1}}}
           } = List.last(target["fun_decls"])

    assert JSON.decode!(LLBCJson.encode_like!(adapted.document, @fixture)) == adapted.document
  end

  test "does not reinterpret an untracked or unsupported dictionary as no-op" do
    doc = @fixture |> File.read!() |> JSON.decode!()

    for dictionary <- ["UntrackedDestruct", "NoopDestruct"] do
      bad =
        alter(doc, fn
          %{"kind" => %{"BuiltinOrAuto" => %{"builtin_data" => "NoopDestruct"}}} = ref ->
            if dictionary == "UntrackedDestruct" do
              put_in(ref, ["kind", "BuiltinOrAuto", "builtin_data"], dictionary)
            else
              put_in(ref, ["trait_decl_ref", "generics", "types"], [
                %{"TypeVar" => %{"Free" => 0}}
              ])
            end

          other ->
            other
        end)

      if dictionary == "UntrackedDestruct" do
        assert %{primitive_models: []} = ExplicitOwnership.prepare!(bad)
      else
        assert_raise ArgumentError, fn -> ExplicitOwnership.prepare!(bad) end
      end
    end
  end

  test "requires intact compiler options, interfaces and declaration identities" do
    doc = @fixture |> File.read!() |> JSON.decode!()

    trait =
      Enum.find_index(
        doc["translated"]["trait_decls"],
        &(&1 && &1["item_meta"]["lang_item"] == "Destruct")
      )

    for bad <- [
          put_in(doc, ["has_errors"], true),
          put_in(doc, ["translated", "options", "precise_drops"], false),
          put_in(doc, ["translated", "options", "desugar_drops"], false),
          put_in(doc, ["translated", "trait_decls", Access.at(trait), "is_unsafe"], true),
          put_in(doc, ["translated", "fun_decls", Access.at(0), "def_id"], 9999)
        ] do
      assert_raise ArgumentError, fn -> ExplicitOwnership.prepare!(bad) end
    end
  end

  test "normal audit closes supplied ownership dictionaries and rejects broken dependencies" do
    doc = @fixture |> File.read!() |> JSON.decode!()
    audit = Lynx.Rust.LLBC.audit!(doc, ["lynx_explicit_scalar"], explicit_ownership: true)
    deps = Lynx.Rust.LLBC.dependencies(audit)
    assert audit.drops == %{erasures: %{}, sites: %{}}
    assert 19 in deps[20]
    assert Enum.any?(audit.compiler_primitives, &(&1.function_id in deps[20]))

    untracked =
      alter(doc, fn
        %{"kind" => %{"BuiltinOrAuto" => %{"builtin_data" => "NoopDestruct"}}} = ref ->
          put_in(ref, ["kind", "BuiltinOrAuto", "builtin_data"], "UntrackedDestruct")

        other ->
          other
      end)

    wrong_self =
      alter(doc, fn
        %{"kind" => %{"BuiltinOrAuto" => %{"builtin_data" => "NoopDestruct"}}} = ref ->
          put_in(ref, ["trait_decl_ref", "generics", "types"], [%{"Deduplicated" => 0}])

        other ->
          other
      end)

    for bad <- [
          untracked,
          wrong_self,
          put_in(doc, ["translated", "fun_decls", Access.at(20), "signature", "is_unsafe"], true)
        ] do
      assert_raise ArgumentError, ~r/explicit Rust ownership/, fn ->
        Lynx.Rust.LLBC.audit!(bad, ["lynx_explicit_scalar"], explicit_ownership: true)
      end
    end

    missing = put_in(doc, ["translated", "fun_decls", Access.at(19), "body"], "Opaque")

    assert_raise CompileError, ~r/missing or unsupported first-party implementation/, fn ->
      Lynx.Rust.LLBC.audit!(missing, ["lynx_explicit_scalar"], explicit_ownership: true)
    end
  end

  @tag timeout: 900_000
  @tag :tmp_dir
  @tag skip: is_nil(@tools) && "set LYNX_UNPATCHED_AENEAS_DIR for explicit ownership proofs"
  test "kernel-checks actual scalar and cross-crate observable destruction", %{tmp_dir: tmp} do
    tools = System.fetch_env!("LYNX_UNPATCHED_AENEAS_DIR")
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app),
        do: File.cp_r!(Path.join(@workspace, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Ownership"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.mkdir_p!(Path.join(project, ".lake"))
    File.ln_s!(packages, Path.join(project, ".lake/packages"))
    properties = File.read!(Path.join(@workspace, "Properties.lean"))
    property = Path.join(project, "Ownership/Properties.lean")
    File.write!(property, properties)

    options = [
      roots: ["ownership_app::run", "ownership_app::run_scalar"],
      owned_drops: :explicit,
      tools: tools,
      build_dir: Path.join(tmp, "build"),
      lean_project: project,
      module_prefix: "Ownership",
      proof_modules: ["Ownership.Properties"],
      required_properties:
        Enum.map(
          ~w(consume_contract scalar_finishes run_panics run_returns),
          &("Ownership.Properties." <> &1)
        )
    ]

    verify = fn ->
      result = Lynx.Rust.verify!(workspace, "ownership-app", options)
      assert [%{status: :ok}] = result.reports
      assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))
      assert result.verification.structural_drops == []
      refute result.verification.compiler_primitives == []

      assert Enum.all?(
               result.verification.compiler_primitives,
               &(&1.implementation_verified == false)
             )

      refute Enum.any?(result.verification.guarantees, &(&1.source_kind == :compiler_primitive))

      assert Enum.any?(
               result.verification.unverified_external_calls,
               &(&1.implementation_verified == false and &1.label =~ "NoopDestruct")
             )

      refute Enum.any?(result.verification.guarantees, fn guarantee ->
               Enum.any?(
                 guarantee.implementation_dependencies,
                 &String.contains?(&1["rust_name"], "LynxCompilerOwnership")
               )
             end)

      input =
        Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules],
          required_properties: options[:required_properties]
        )

      {input, result.extraction}
    end

    {input, extraction} = verify.()
    refute extraction.explicit_ownership.primitive_models == []
    raw = project |> Path.join("Ownership.llbc") |> File.read!() |> JSON.decode!()
    functions = raw["translated"]["fun_decls"]

    glue =
      Enum.find_index(functions, fn f ->
        f && Lynx.Rust.DropModels.generated?(f) &&
          hd(f["item_meta"]["name"]) == %{"Ident" => ["ownership_base", 0]}
      end)

    assert is_integer(glue)

    for bad <- [
          put_in(raw, ["translated", "fun_decls", Access.at(glue), "src"], "Normal"),
          put_in(raw, ["translated", "fun_decls", Access.at(glue), "body"], "Opaque")
        ] do
      assert_raise ArgumentError, ~r/explicit Rust ownership/, fn ->
        Lynx.Rust.LLBC.audit!(bad, ["ownership_app", "ownership_base"], explicit_ownership: true)
      end
    end

    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [input])

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "ownership-app", options).reports

    export = Path.join(tmp, "ownership.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [input], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom hiddenOwnership : False",
          "private theorem unfinishedOwnership : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> extra <> "\n")
      Lynx.Rust.Project.build!(project, ["Ownership.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [input])
    end

    File.write!(
      property,
      properties <>
        """

        theorem Ownership.Properties.noop_only (value : U64) :
            LynxCompilerOwnership.noop value = RustM.ok value := by rfl
        """
    )

    Lynx.Rust.Project.build!(project, ["Ownership.Properties"])

    primitive_only =
      Lynx.Rust.Proofs.file!(extraction, options[:proof_modules],
        required_properties: ["Ownership.Properties.noop_only"]
      )

    assert [%{status: :error, diagnostics: diagnostics}] =
             Lynx.Commands.verify!(project, [primitive_only])

    assert Enum.any?(
             diagnostics,
             &String.contains?(&1.message, "has no extracted implementation")
           )

    File.write!(property, properties)
    source = Path.join(workspace, "base/src/lib.rs")
    original = File.read!(source)
    File.write!(source, String.replace(original, "self.code != 7", "self.code != 8"))
    assert_raise RuntimeError, ~r/native Lean project command failed/, fn -> verify.() end
    File.write!(source, original)
    assert {_, _} = verify.()
  end

  defp erase_witness(
         %{
           "kind" => %{"BuiltinOrAuto" => %{"builtin_data" => "NoopDestruct"}},
           "trait_decl_ref" => declaration
         },
         _
       ),
       do: %{"dictionary" => declaration}

  defp erase_witness(
         %{"kind" => %{"TraitImpl" => %{"id" => id}}, "trait_decl_ref" => declaration} = map,
         ids
       ) do
    if id in ids,
      do: %{"dictionary" => declaration},
      else: Map.new(map, fn {k, v} -> {k, erase_witness(v, ids)} end)
  end

  defp erase_witness(map, ids) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, erase_witness(v, ids)} end)

  defp erase_witness(list, ids) when is_list(list), do: Enum.map(list, &erase_witness(&1, ids))
  defp erase_witness(value, _), do: value

  defp alter(map, fun) when is_map(map) do
    changed = fun.(map)
    if changed != map, do: changed, else: Map.new(map, fn {k, v} -> {k, alter(v, fun)} end)
  end

  defp alter(list, fun) when is_list(list), do: Enum.map(list, &alter(&1, fun))
  defp alter(value, _), do: value
end
