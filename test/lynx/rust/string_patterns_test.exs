defmodule Lynx.Rust.StringPatternsTest do
  use ExUnit.Case, async: true

  alias Lynx.Rust.{
    CallModels,
    LibraryHelpers,
    LLBC,
    LLBCJson,
    ResourceModels,
    StringPatterns,
    StringSliceModels
  }

  @snapshot Path.expand("../../fixtures/rustler/string_prefix.json", __DIR__)

  setup do
    doc = JSON.decode!(File.read!(@snapshot)) |> put_in(["translated", "files"], [])
    audit = LLBC.audit!(doc, ~w(experiment_core experiment_analysis))
    t = doc["translated"]
    helpers = Enum.filter(t["fun_decls"], &(&1 && StringPatterns.selected?(&1, t)))
    method = Enum.find(helpers, &is_map(&1["src"]))
    start = Enum.find(helpers, &(&1["src"] == "Normal"))
    %{doc: doc, t: t, audit: audit, method: method, start: start}
  end

  test "preserves the actual implementations and first-party bodies while projecting the unused interface",
       c do
    assert c.method && c.start
    assert LibraryHelpers.selected?(c.method, c.t)
    {projected, view} = StringPatterns.project!(c.doc, c.audit)
    assert view.methods == [2]

    for f <- c.audit.functions do
      kept = Enum.find(projected["translated"]["fun_decls"], &(&1 && &1["def_id"] == f["def_id"]))
      assert kept
      assert kept["item_meta"]["name"] == f["item_meta"]["name"]
    end

    trait = Enum.find(projected["translated"]["trait_decls"], &(&1 && &1["def_id"] == view.trait))
    assert [] = trait["types"]
    assert [%{"skip_binder" => %{"name" => "is_prefix_of", "default" => nil}}] = trait["methods"]

    assert Enum.at(projected["translated"]["assoc_item_names"], view.trait)["methods"] == [
             "is_prefix_of"
           ]
  end

  test "rejects missing implementations, changed signatures and mismatched method bindings", c do
    for f <- [c.method, c.start],
        changed <- [
          Map.put(f, "body", "Opaque"),
          put_in(f, ["signature", "is_unsafe"], true),
          put_in(f, ["signature", "inputs"], []),
          put_in(f, ["signature", "output"], %{"Scalar" => "BoolChanged"}),
          put_in(f, ["signature", "abi"], "C"),
          put_in(f, ["generics", "outlives"], [%{}])
        ] do
      refute StringPatterns.selected?(changed, c.t)
    end

    doc =
      update_in(c.doc, ["translated", "fun_decls"], fn fs ->
        Enum.map(fs, fn f -> if f == c.method, do: Map.put(f, "body", "Opaque"), else: f end)
      end)

    assert_raise CompileError, ~r/shared-str prefix/, fn ->
      LLBC.audit!(doc, ~w(experiment_core experiment_analysis))
    end
  end

  test "rejects another Pattern operation before projection", c do
    doc =
      update_in(c.doc, ["translated", "fun_decls"], fn fs ->
        Enum.map(fs, fn f ->
          if f == c.start, do: update_in(f, ["body"], &replace_method/1), else: f
        end)
      end)

    assert_raise CompileError, ~r/shared-str prefix/, fn ->
      LLBC.audit!(doc, ~w(experiment_core experiment_analysis))
    end
  end

  test "does not project an observed searcher value from first-party signatures", c do
    searcher =
      Enum.find(
        c.t["type_decls"],
        &(&1 && List.last(&1["item_meta"]["name"]) == %{"Ident" => ["StrSearcher", 0]})
      )

    assert searcher

    hydrated =
      c.doc
      |> LLBCJson.restore_type_references!(c.doc)
      |> LLBCJson.restore_trait_references!(c.doc)

    doc =
      update_in(hydrated, ["translated", "fun_decls"], fn fs ->
        Enum.map(fs, fn f ->
          if f && f["def_id"] == hd(c.audit.functions)["def_id"],
            do:
              put_in(f, ["signature", "inputs"], [
                %{
                  "Adt" => %{
                    "id" => searcher["def_id"],
                    "builtin" => nil,
                    "generics" => Lynx.Rust.ResourceModels.args([])
                  }
                }
              ]),
            else: f
        end)
      end)

    assert_raise ArgumentError, ~r/observed foreign searcher/, fn ->
      StringPatterns.project!(doc, c.audit)
    end
  end

  test "retains both actual prefix methods for standard prefix consumption" do
    doc = consume_snapshot()
    audit = LLBC.audit!(doc, ~w(experiment_core experiment_analysis))
    {projected, view} = StringPatterns.project!(doc, audit)
    assert view.methods == [2, 4]
    trait = Enum.find(projected["translated"]["trait_decls"], &(&1 && &1["def_id"] == view.trait))

    assert Enum.map(trait["methods"], & &1["skip_binder"]["name"]) ==
             ["is_prefix_of", "strip_prefix_of"]

    for original <- audit.functions,
        original["src"] == "Normal",
        hd(original["item_meta"]["name"]) in [
          %{"Ident" => ["experiment_core", 0]},
          %{"Ident" => ["experiment_analysis", 0]}
        ] do
      kept =
        Enum.find(
          projected["translated"]["fun_decls"],
          &(&1 && &1["def_id"] == original["def_id"])
        )

      hydrated =
        doc |> LLBCJson.restore_type_references!(doc) |> LLBCJson.restore_trait_references!(doc)

      before =
        Enum.find(
          hydrated["translated"]["fun_decls"],
          &(&1 && &1["def_id"] == original["def_id"])
        )

      assert Map.take(kept, ~w(body signature)) == Map.take(before, ~w(body signature))
    end
  end

  test "rejects direct first-party calls to the unchecked borrow model" do
    doc = consume_snapshot()
    audit = LLBC.audit!(doc, ~w(experiment_core experiment_analysis))
    stripper = Enum.find(audit.functions, &get_in_source(&1, 4))
    call = find_unchecked_call(stripper["body"], doc["translated"])
    assert call
    target = Enum.find(audit.functions, &(&1["item_meta"]["is_local"] == true))
    assert target

    altered =
      update_in(doc, ["translated", "fun_decls"], fn fs ->
        Enum.map(fs, fn f ->
          if f && f["def_id"] == target["def_id"], do: %{f | "body" => call}, else: f
        end)
      end)

    assert_raise CompileError, ~r/unchecked string borrowing is restricted/, fn ->
      LLBC.audit!(altered, ~w(experiment_core experiment_analysis))
    end
  end

  test "validates the unchecked range dictionary and raw-pointer signature before admitting the model" do
    doc = consume_snapshot()
    t = doc["translated"]
    refs = LLBC.type_references!(t)
    models = CallModels.resolve(t["fun_decls"], t, refs, [])

    stripper =
      Enum.find(t["fun_decls"], &(&1 && StringPatterns.selected?(&1, t) && get_in_source(&1, 4)))

    call = find_unchecked_call(stripper["body"], t)
    actual = call["Call"]["call"]["func"]["Regular"]["generics"]
    traits = ResourceModels.trait_references(t)
    id = StringSliceModels.unchecked_from_call!(actual, models, t, refs, traits)
    assert is_integer(id)

    for broken <- [
          Map.put(actual, "trait_refs", []),
          Map.update!(actual, "types", &Enum.reverse/1)
        ] do
      assert_raise ArgumentError, fn ->
        StringSliceModels.unchecked_from_call!(broken, models, t, refs, traits)
      end
    end

    for field <- ~w(inputs output abi is_unsafe is_variadic) do
      altered =
        update_in(models, [id, :function, "signature", field], fn
          value when is_list(value) -> []
          value when is_boolean(value) -> not value
          _ -> "changed"
        end)

      assert_raise ArgumentError, ~r/unchecked RangeFrom/, fn ->
        StringSliceModels.unchecked_from_call!(actual, altered, t, refs, traits)
      end
    end
  end

  defp consume_snapshot do
    Path.expand("../../fixtures/rustler/string_consume_prefix.json", __DIR__)
    |> File.read!()
    |> JSON.decode!()
    |> put_in(["translated", "files"], [])
  end

  defp get_in_source(%{"src" => %{"TraitImpl" => %{"item_id" => slot}}}, slot), do: true
  defp get_in_source(_, _), do: false

  defp find_unchecked_call(
         %{"Call" => %{"call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => id}}}}}} = call,
         t
       ) do
    target = Enum.find(t["fun_decls"], &(&1 && &1["def_id"] == id))

    if target && List.last(target["item_meta"]["name"]) == %{"Ident" => ["get_unchecked", 0]},
      do: call
  end

  defp find_unchecked_call(m, t) when is_map(m), do: find_unchecked_call(Map.values(m), t)

  defp find_unchecked_call(l, t) when is_list(l),
    do: Enum.find_value(l, &find_unchecked_call(&1, t))

  defp find_unchecked_call(_, _), do: nil

  defp replace_method(%{"Trait" => [raw, 2]} = m), do: %{m | "Trait" => [raw, 3]}
  defp replace_method(m) when is_map(m), do: Map.new(m, fn {k, v} -> {k, replace_method(v)} end)
  defp replace_method(l) when is_list(l), do: Enum.map(l, &replace_method/1)
  defp replace_method(v), do: v
end
