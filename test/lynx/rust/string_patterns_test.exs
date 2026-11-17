defmodule Lynx.Rust.StringPatternsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{LibraryHelpers, LLBC, LLBCJson, StringPatterns}
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
    assert view.method == 2

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

  defp replace_method(%{"Trait" => [raw, 2]} = m), do: %{m | "Trait" => [raw, 3]}
  defp replace_method(m) when is_map(m), do: Map.new(m, fn {k, v} -> {k, replace_method(v)} end)
  defp replace_method(l) when is_list(l), do: Enum.map(l, &replace_method/1)
  defp replace_method(v), do: v
end
