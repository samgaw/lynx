defmodule Lynx.Rustler.AtomConstructorsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rustler.ErrorConstructors
  @snapshot Path.expand("../../fixtures/rustler/atom_constructors.json", __DIR__)
  @crates ~w(experiment_nif experiment_analysis experiment_core experiment_unrelated)

  setup do
    data = @snapshot |> File.read!() |> JSON.decode!()
    %{document: data["document"], layout: data["layout"]}
  end

  test "retains compiled literal loads and opaque types while modelling only the constructors",
       ctx do
    {doc, %{values: values} = proof} =
      ErrorConstructors.lower!(ctx.document, ctx.layout, @crates, "Snapshot")

    assert Enum.sort(Enum.map(values.entries, &{&1.variant, &1.literal})) == [
             {"Atom", "zero"},
             {"RaiseAtom", "zero"}
           ]

    assert doc["translated"]["type_decls"] == ctx.document["translated"]["type_decls"]
    assert loads(doc) == loads(ctx.document)

    assert [%{implementation_verified: false}, %{implementation_verified: false}] =
             Map.values(ErrorConstructors.models!(doc, proof))

    refute ErrorConstructors.needed?(doc, @crates)
    [entry | _] = values.entries

    doc =
      update_in(
        doc,
        ["translated", "fun_decls"],
        &List.replace_at(&1, entry.declaration["def_id"], nil)
      )

    assert_raise ArgumentError, ~r/inconsistent validated Rustler atom primitive/, fn ->
      ErrorConstructors.models!(doc, proof)
    end
  end

  test "rejects changed compiled variant IDs, payloads and lifetimes", ctx do
    for change <- [
          &Map.put(&1, "id", -1),
          &Map.put(&1, "fields", []),
          &put_in(&1, ["fields", Access.at(0), "ty"], %{"Ref" => ["Erased", %{}, "Shared"]})
        ] do
      layout =
        update_in(ctx.layout, ["translated", "type_decls"], fn types ->
          Enum.map(types, fn
            %{"kind" => %{"Enum" => variants}} = type ->
              put_in(
                type,
                ["kind", "Enum"],
                Enum.map(variants, fn variant ->
                  if variant["name"] == "Atom", do: change.(variant), else: variant
                end)
              )

            type ->
              type
          end)
        end)

      assert_raise ArgumentError, fn ->
        ErrorConstructors.lower!(ctx.document, layout, @crates)
      end
    end
  end

  test "rejects inconsistent literal length and mutable global provenance", ctx do
    for change <- [
          &put_in(&1, ["value", "Value", Access.at(1), Access.at(0), "Str"], "different"),
          &Map.put(&1, "global_kind", "Static")
        ] do
      doc =
        update_in(ctx.document, ["translated", "global_decls"], fn globals ->
          Enum.map(globals, fn
            %{"global_kind" => "AnonConst", "value" => %{"Value" => [_, [%{"Str" => _}, _]]}} =
                global ->
              change.(global)

            global ->
              global
          end)
        end)

      assert_raise CompileError, ~r/validated ASCII literal/, fn ->
        ErrorConstructors.lower!(doc, ctx.layout, @crates)
      end
    end
  end

  test "names unsupported payload constructors using the compiled enum layout", ctx do
    error =
      Enum.find(
        ctx.layout["translated"]["type_decls"],
        &(&1 && match?(%{"Enum" => _}, &1["kind"]))
      )

    variants = error["kind"]["Enum"]
    atom = Enum.find(variants, &(&1["name"] == "Atom"))
    raised = Enum.find(variants, &(&1["name"] == "RaiseTerm"))
    doc = replace_variant(ctx.document, atom["id"], raised["id"])

    assert_raise CompileError,
                 ~r/Rustler RaiseTerm requires a validated boxed Encoder/,
                 fn ->
                   ErrorConstructors.lower!(doc, ctx.layout, @crates)
                 end

    layout =
      update_in(ctx.layout, ["translated", "type_decls"], fn types ->
        Enum.map(types, fn type ->
          if type == error do
            put_in(
              type,
              ["kind", "Enum"],
              Enum.map(variants, fn v ->
                if v == raised, do: %{v | "name" => "OtherPayload"}, else: v
              end)
            )
          else
            type
          end
        end)
      end)

    assert_raise CompileError, ~r/Error::OtherPayload construction/, fn ->
      ErrorConstructors.lower!(doc, layout, @crates)
    end
  end

  defp replace_variant(%{"Aggregate" => [%{"Adt" => [type, old, extra]}, operands]}, old, new),
    do: %{"Aggregate" => [%{"Adt" => [type, new, extra]}, operands]}

  defp replace_variant(map, old, new) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, replace_variant(value, old, new)} end)

  defp replace_variant(list, old, new) when is_list(list),
    do: Enum.map(list, &replace_variant(&1, old, new))

  defp replace_variant(value, _, _), do: value

  defp loads(%{"Ref" => %{"kind" => "Shared"} = ref} = map),
    do: [ref | Enum.flat_map(Map.values(map), &loads/1)]

  defp loads(map) when is_map(map), do: Enum.flat_map(Map.values(map), &loads/1)
  defp loads(list) when is_list(list), do: Enum.flat_map(list, &loads/1)
  defp loads(_), do: []
end
