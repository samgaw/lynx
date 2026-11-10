defmodule Lynx.Rustler.PayloadConstructorsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LLBC, LLBCJson, VTables}
  alias Lynx.Rustler.ErrorConstructors
  @snapshot Path.expand("../../fixtures/rustler/payload_constructor.json", __DIR__)
  @crates ~w(experiment_nif experiment_analysis experiment_core experiment_unrelated)
  setup do
    data = @snapshot |> File.read!() |> JSON.decode!()
    %{document: data["document"], layout: data["layout"]}
  end

  test "preserves executable operands and drops while adapting the foreign signature", ctx do
    {lowered, %{values: %{entries: [entry]}} = proof} =
      ErrorConstructors.lower!(ctx.document, ctx.layout, @crates, "Payload")

    assert entry.variant == "RaiseTerm"
    assert entry.literal == nil
    assert counts(lowered) == counts(ctx.document)
    assert lowered["translated"]["type_decls"] == ctx.document["translated"]["type_decls"]

    assert %{
             lean: "Lynx.Rustler.raiseTermErrorOutcome",
             can_fail: false,
             implementation_verified: false
           } = ErrorConstructors.models!(lowered, proof)[entry.declaration["def_id"]]

    [input] = entry.declaration["signature"]["inputs"]
    refs = LLBC.type_references!(lowered)

    %{"Adt" => %{"generics" => %{"types" => [%{"DynTrait" => predicate}]}}} =
      CallModels.expand(input, refs)

    assert [%{"skip_binder" => [_, "Erased"]}] = predicate["binder"]["params"]["outlives"]
    refute ErrorConstructors.needed?(lowered, @crates)
  end

  test "checks the actual boxed field and Encoder trait identity", ctx do
    for name <- ["RaiseTerm"] do
      layout =
        update_in(ctx.layout, ["translated", "type_decls"], fn types ->
          Enum.map(types, fn
            %{"kind" => %{"Enum" => variants}} = type ->
              put_in(
                type,
                ["kind", "Enum"],
                Enum.map(variants, fn variant ->
                  if variant["name"] == name, do: %{variant | "fields" => []}, else: variant
                end)
              )

            type ->
              type
          end)
        end)

      assert_raise CompileError, ~r/validated boxed Encoder/, fn ->
        ErrorConstructors.lower!(ctx.document, layout, @crates)
      end
    end

    doc =
      update_in(ctx.document, ["translated", "trait_decls"], fn traits ->
        Enum.map(traits, fn trait ->
          if trait &&
               trait["item_meta"]["name"] ==
                 Enum.map(~w(rustler types Encoder), &%{"Ident" => [&1, 0]}),
             do: put_in(trait, ["is_unsafe"], true),
             else: trait
        end)
      end)

    assert_raise CompileError, ~r/validated boxed Encoder/, fn ->
      ErrorConstructors.lower!(doc, ctx.layout, @crates)
    end
  end

  test "validates the two-lifetime Encoder shim and rejects altered ABI arguments", ctx do
    doc = ctx.document
    translated = doc["translated"]
    refs = LLBC.type_references!(doc)

    globals =
      Enum.filter(translated["global_decls"], &(&1 && &1["item_meta"]["is_local"]))
      |> LLBCJson.restore_global_constant_values!(doc)

    functions = Enum.filter(translated["fun_decls"], &(&1 && &1["item_meta"]["is_local"]))
    {tables, _, _} = VTables.audit!(globals, functions, translated, refs)
    [table] = Map.values(tables)
    assert %{external_trait: "rustler::types::Encoder", shims: [_, method]} = table["lynx_vtable"]

    changed =
      update_in(
        translated,
        ["fun_decls"],
        &Enum.map(&1, fn f ->
          if f && f["def_id"] == method, do: put_in(f, ["signature", "abi"], "C"), else: f
        end)
      )

    assert_raise ArgumentError, ~r/compiler vtable metadata/, fn ->
      VTables.audit!(globals, functions, changed, refs)
    end
  end

  defp counts(%{"kind" => %{"Drop" => _}} = map),
    do: ["drop" | Enum.flat_map(Map.values(map), &counts/1)]

  defp counts(%{"Unsize" => _} = map), do: ["unsize" | Enum.flat_map(Map.values(map), &counts/1)]
  defp counts(map) when is_map(map), do: Enum.flat_map(Map.values(map), &counts/1)
  defp counts(list) when is_list(list), do: Enum.flat_map(list, &counts/1)
  defp counts(_), do: []
end
