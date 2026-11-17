defmodule Lynx.Rust.OrderedIteratorModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LLBC, LLBCJson, OrderedIteratorModels}
  @fixture Path.expand("../../fixtures/rustler/ordered_iterators.json", __DIR__)
  @crates ~w(experiment_core experiment_analysis)

  setup do
    doc = @fixture |> File.read!() |> JSON.decode!() |> put_in(["translated", "files"], [])
    t = doc["translated"]
    refs = LLBC.type_references!(t)
    models = CallModels.resolve(t["fun_decls"], t, refs, [])
    %{doc: doc, t: t, refs: refs, models: models, audit: LLBC.audit!(doc, @crates)}
  end

  test "admits compiled shared map/set iteration as explicit external models", c do
    models = Enum.filter(Map.values(c.models), & &1[:ordered_iterator])

    assert Enum.sort(Enum.map(models, &{&1.ordered_iterator, &1.ordered_iterator_method})) ==
             for(family <- ~w(map set), method <- ~w(into_iter next), do: {family, method})

    assert Enum.all?(
             models,
             &(&1.status == :modelled and not &1.implementation_verified and &1.native_cutoff_only)
           )

    assert Enum.sort(c.audit.ordered_iterators.families) == ~w(map set)
    assert Enum.any?(Map.values(c.models), & &1[:slice_first])
  end

  test "rejects changed ABI, mutability, generic bounds and method identities", c do
    for model <- Map.values(c.models),
        model[:ordered_iterator],
        f = model.function,
        changed <- [
          put_in(f, ["signature", "abi"], "C"),
          put_in(f, ["signature", "is_unsafe"], true),
          put_in(f, ["signature", "inputs"], []),
          put_in(f, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(f, ["generics", "outlives"], []),
          put_in(f, ["src", "TraitImpl", "reuses_default"], true),
          put_in(f, ["src", "TraitImpl", "item_id"], 1)
        ] do
      refute OrderedIteratorModels.resolve(changed, c.t, c.refs)
    end
  end

  test "requires the actual next dependency and its forwarding lifetimes", c do
    ctx = OrderedIteratorModels.context(c.t, c.refs)

    for family <- ~w(map set) do
      model =
        Enum.find_value(c.models, fn {_, m} ->
          if m[:ordered_iterator] == family and m[:ordered_iterator_method] == "into_iter", do: m
        end)

      impl = model.function["src"]["TraitImpl"]["impl_ref"]["id"]

      for changed <- [
            update(c.doc, "trait_impls", impl, &Map.put(&1, "implied_trait_refs", [])),
            update(c.doc, "trait_impls", impl, &put_in(&1, ["methods"], []))
          ] do
        t = changed["translated"]

        refute OrderedIteratorModels.resolve(
                 Enum.find(t["fun_decls"], &(&1 && &1["def_id"] == model.definition_id)),
                 t,
                 LLBC.type_references!(t)
               )
      end

      id = ctx.iterators[family]

      changed =
        update(
          c.doc,
          "type_decls",
          id,
          &put_in(&1, ["generics", "regions", Access.at(0), "mutability"], "Mut")
        )

      assert_raise CompileError, ~r/ordered iterator representation|unverified external/, fn ->
        LLBC.audit!(changed, @crates)
      end
    end
  end

  test "checks standard allocator and concrete iterator element arguments", c do
    owner = hd(c.audit.functions)

    model =
      Enum.find_value(c.models, fn {_, m} ->
        if m[:ordered_iterator_method] == "into_iter", do: m
      end)

    malformed =
      Map.put(owner, "body", %{
        "Regular" => %{
          "kind" => %{"Fun" => model.definition_id},
          "generics" => %{
            "regions" => [%{"Body" => 0}],
            "types" => [],
            "const_generics" => [],
            "trait_refs" => []
          }
        }
      })

    assert {:error, _, message} =
             OrderedIteratorModels.audit([malformed], c.models, c.t, c.refs, @crates, :pure)

    assert message =~ "concrete u64"
  end

  test "conditional vector cleanup requires checked scalar or compiler Copy evidence", c do
    entries =
      c.audit.drops.erasures |> Map.values() |> Enum.flat_map(&Map.get(&1, :instances, [&1]))

    assert Enum.any?(entries, fn m ->
             match?(%{kind: :compiler_copy}, m[:element_drop_basis]) and
               m.supported_drop_kinds == ~w(Precise Conditional)
           end)

    assert Enum.any?(entries, &(&1[:element_drop_basis] == :primitive_scalar))
    copy = Enum.find(c.t["trait_decls"], &(&1 && &1["item_meta"]["lang_item"] == "Copy"))

    entry =
      Enum.find(
        c.t["type_decls"],
        &(&1 && List.last(&1["item_meta"]["name"]) == %{"Ident" => ["Entry", 0]})
      )

    entry_id = entry["def_id"]

    impl =
      Enum.find(c.t["trait_impls"], fn i ->
        i && i["impl_trait"]["id"] == copy["def_id"] &&
          match?(
            [%{"Adt" => %{"id" => ^entry_id}}],
            CallModels.expand(i["impl_trait"]["generics"]["types"], c.refs)
          )
      end)

    changed = update(c.doc, "trait_impls", impl["def_id"], &Map.put(&1, "is_negative", true))

    assert_raise CompileError, ~r/conditional Vec drop requires.*Copy/, fn ->
      LLBC.audit!(changed, @crates)
    end
  end

  test "rejects inconsistent slice first signatures", c do
    model = Enum.find_value(c.models, fn {_, m} -> if m[:slice_first], do: m end)
    assert not model.implementation_verified
    f = model.function

    refute Lynx.Rust.SliceModels.resolve(
             put_in(f, ["signature", "output"], %{"Scalar" => "Bool"}),
             c.t,
             c.refs
           )

    refute Lynx.Rust.SliceModels.resolve(put_in(f, ["signature", "is_unsafe"], true), c.t, c.refs)
  end

  test "admits validated shared cursors in runtime computations", c do
    assert {:ok, %{families: families}} =
             OrderedIteratorModels.audit(
               c.audit.functions,
               c.models,
               c.t,
               c.refs,
               @crates,
               :runtime
             )

    assert Enum.sort(families) == ~w(map set)
  end

  defp update(doc, key, id, change) do
    hydrated =
      doc
      |> LLBCJson.restore_type_references!(doc)
      |> LLBCJson.restore_trait_references!(doc)
      |> LLBCJson.restore_constant_references!(doc)

    update_in(
      hydrated,
      ["translated", key],
      &Enum.map(&1, fn d -> if d && d["def_id"] == id, do: change.(d), else: d end)
    )
  end
end
