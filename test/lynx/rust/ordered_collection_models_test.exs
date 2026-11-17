defmodule Lynx.Rust.OrderedCollectionModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, ComparisonInterfaces, LLBC, LLBCJson, OrderedCollectionModels}
  @snapshot Path.expand("../../fixtures/rustler/ordered_collections.json", __DIR__)
  @crates ~w(experiment_core experiment_analysis)

  setup do
    doc = @snapshot |> File.read!() |> JSON.decode!() |> put_in(["translated", "files"], [])
    t = doc["translated"]
    refs = LLBC.type_references!(t)
    models = CallModels.resolve(t["fun_decls"], t, refs, [])
    audit = LLBC.audit!(doc, @crates)
    %{doc: doc, t: t, refs: refs, models: models, audit: audit}
  end

  test "admits the compiled scalar map/set operations as explicit models", c do
    supported =
      for {_, m} <- c.models,
          m[:ordered_collection],
          do: {m.ordered_collection, m.ordered_method, m}

    assert Enum.sort(for {f, m, _} <- supported, do: {f, m}) ==
             Enum.sort(
               for(f <- ~w(map set), m <- ~w(insert len new remove), do: {f, m}) ++
                 [{"map", "get"}, {"set", "contains"}]
             )

    assert Enum.all?(supported, fn {_, _, m} ->
             m.status == :modelled and not m.implementation_verified
           end)

    assert Enum.sort(c.audit.ordered_collections.families) == ~w(map set)

    assert Enum.all?(
             Map.values(c.audit.drops.erasures),
             &(&1.status == :modelled and not &1.implementation_verified)
           )

    assert Enum.any?(
             Map.values(c.audit.drops.erasures),
             &(&1[:supported_drop_kinds] == ~w(Precise Conditional))
           )
  end

  test "rejects altered operation ABI, generic shape and nominal representations", c do
    for {_, m} <- c.models,
        m[:ordered_collection],
        f = m.function,
        changed <- [
          put_in(f, ["signature", "is_unsafe"], true),
          put_in(f, ["signature", "abi"], "C"),
          put_in(f, ["signature", "inputs"], [%{}]),
          put_in(f, ["signature", "output"], %{"Scalar" => "Changed"}),
          put_in(f, ["generics", "const_generics"], [%{}]),
          put_in(f, ["item_meta", "name"], [])
        ] do
      refute OrderedCollectionModels.resolve(changed, c.t, c.refs)
    end

    id = c.audit.ordered_collections.types["map"]
    doc = update_declaration(c.doc, "type_decls", id, &Map.put(&1, "kind", %{"Struct" => []}))

    assert_raise CompileError, ~r/ordered collection representation|unverified external/, fn ->
      LLBC.audit!(doc, @crates)
    end
  end

  test "rejects missing or inconsistent ordering implementations", c do
    ctx = OrderedCollectionModels.context(c.t, c.refs)

    impl =
      Enum.find(
        c.t["trait_impls"],
        &((&1 && &1["impl_trait"]["id"] == ctx.traits["Ord"]) and &1["generics"]["types"] == [])
      )

    cmp = hd(impl["methods"])["skip_binder"]["id"]

    for doc <- [
          update_declaration(c.doc, "trait_impls", impl["def_id"], &Map.put(&1, "methods", [])),
          update_declaration(
            c.doc,
            "fun_decls",
            cmp,
            &put_in(&1, ["signature", "is_unsafe"], true)
          ),
          update_declaration(c.doc, "fun_decls", cmp, &put_in(&1, ["signature", "inputs"], []))
        ] do
      assert_raise CompileError, ~r/ordered collection dictionary/, fn ->
        LLBC.audit!(doc, @crates)
      end
    end
  end

  test "validates identity Borrow and both lookup lifetimes", c do
    ctx = OrderedCollectionModels.context(c.t, c.refs)
    impl = Enum.find(c.t["trait_impls"], &(&1 && &1["impl_trait"]["id"] == ctx.traits["Borrow"]))
    pointer = hd(impl["methods"])["skip_binder"]
    helper = Enum.find(c.t["fun_decls"], &(&1 && &1["def_id"] == pointer["id"]))
    assert Lynx.Rust.LibraryHelpers.selected?(helper, c.t)
    refute Lynx.Rust.LibraryHelpers.selected?(%{helper | "src" => "Normal"}, c.t)

    for doc <- [
          update_declaration(c.doc, "trait_impls", impl["def_id"], &Map.put(&1, "methods", [])),
          update_declaration(
            c.doc,
            "trait_impls",
            impl["def_id"],
            &Map.put(&1, "is_unsafe", true)
          ),
          update_declaration(
            c.doc,
            "fun_decls",
            pointer["id"],
            &put_in(&1, ["signature", "output"], %{"Scalar" => "Bool"})
          ),
          update_declaration(
            c.doc,
            "trait_impls",
            impl["def_id"],
            &put_in(&1, ["impl_trait", "generics", "types"], [])
          )
        ] do
      assert_raise CompileError, ~r/ordered collection Borrow dictionary/, fn ->
        LLBC.audit!(doc, @crates)
      end
    end

    for {_, model} <- c.models, model[:ordered_method] in ~w(get contains remove) do
      f = model.function
      signature = CallModels.expand(f["signature"], c.refs)
      [self, %{"Ref" => [region, query, mode]}] = signature["inputs"]
      assert region == %{"Var" => %{"Free" => 1}}

      changed =
        put_in(f, ["signature", "inputs"], [
          self,
          %{"Ref" => [%{"Var" => %{"Free" => 0}}, query, mode]}
        ])

      refute OrderedCollectionModels.resolve(changed, c.t, c.refs)
      refute OrderedCollectionModels.resolve(put_in(f, ["generics", "outlives"], []), c.t, c.refs)
    end
  end

  test "retains only actual shared Option copied helper bodies", c do
    helper =
      Enum.find(c.t["fun_decls"], fn f ->
        f && List.last(f["item_meta"]["name"]) == %{"Ident" => ["copied", 0]}
      end)

    assert Lynx.Rust.LibraryHelpers.selected?(helper, c.t)
    refute Lynx.Rust.LibraryHelpers.selected?(%{helper | "body" => "Opaque"}, c.t)
    sig = CallModels.expand(helper["signature"], c.refs)
    [%{"Adt" => %{"id" => id, "generics" => args} = option}] = sig["inputs"]
    [%{"Ref" => [region, item, "Shared"]}] = args["types"]

    mutated =
      put_in(helper, ["signature", "inputs"], [
        %{
          "Adt" => %{
            option
            | "generics" => %{args | "types" => [%{"Ref" => [region, item, "Mut"]}]}
          }
        }
      ])

    refute Lynx.Rust.OptionModels.copied_helper?(mutated, c.t)

    t =
      update_in(
        c.t,
        ["type_decls"],
        &Enum.map(&1, fn d ->
          if d && d["def_id"] == id, do: %{d | "kind" => "Opaque"}, else: d
        end)
      )

    refute Lynx.Rust.OptionModels.copied_helper?(helper, t)
  end

  test "checks compiler drop signatures and forwarding dictionaries", c do
    [id | _] = Map.keys(c.audit.drops.erasures)

    for doc <- [
          update_declaration(
            c.doc,
            "fun_decls",
            id,
            &put_in(&1, ["signature", "is_unsafe"], false)
          ),
          update_declaration(
            c.doc,
            "fun_decls",
            id,
            &put_in(&1, ["src", "TraitImpl", "impl_ref", "generics", "trait_refs"], [])
          )
        ] do
      assert_raise CompileError, ~r/ordered collection drop/, fn -> LLBC.audit!(doc, @crates) end
    end
  end

  test "preserves audited bodies and signatures while omitting only unobserved foreign helpers",
       c do
    {projected, info} = ComparisonInterfaces.project!(c.doc, c.audit)
    assert length(info.omitted) > 0

    before =
      c.doc
      |> LLBCJson.restore_type_references!(c.doc)
      |> LLBCJson.restore_trait_references!(c.doc)
      |> LLBCJson.restore_constant_references!(c.doc)
      |> LLBCJson.restore_spans!(c.doc)

    for f <- c.audit.functions do
      original =
        Enum.find(before["translated"]["fun_decls"], &(&1 && &1["def_id"] == f["def_id"]))

      kept = Enum.find(projected["translated"]["fun_decls"], &(&1 && &1["def_id"] == f["def_id"]))
      assert Map.take(original, ~w(body signature)) == Map.take(kept, ~w(body signature))
    end

    for d <- projected["translated"]["trait_decls"],
        d,
        d["def_id"] in info.traits,
        do:
          refute(
            Enum.any?(
              d["methods"],
              &(&1["skip_binder"]["name"] in ~w(clamp_to __chaining_lt assert_receiver_is_total_eq))
            )
          )
  end

  test "refuses to omit an observed function or method", c do
    {_, info} = ComparisonInterfaces.project!(c.doc, c.audit)
    id = hd(info.omitted)
    owner = hd(c.audit.functions)

    doc =
      update_declaration(
        c.doc,
        "fun_decls",
        owner["def_id"],
        &Map.put(&1, "body", %{"Regular" => %{"kind" => %{"Fun" => id}}})
      )

    assert_raise ArgumentError, ~r/observed omitted/, fn ->
      ComparisonInterfaces.project!(doc, c.audit)
    end

    helper = Enum.find(c.t["fun_decls"], &(&1 && &1["def_id"] == id))
    source = helper["src"]["TraitImpl"] || helper["src"]["TraitDefault"]
    dictionary = %{"Value" => [0, %{"trait_decl_ref" => source["trait_ref"]}]}

    observed_method =
      update_declaration(
        c.doc,
        "fun_decls",
        owner["def_id"],
        &Map.put(&1, "body", %{"Trait" => [dictionary, source["item_id"]]})
      )

    assert_raise ArgumentError, ~r/observed omitted comparison method/, fn ->
      ComparisonInterfaces.project!(observed_method, c.audit)
    end
  end

  test "admits runtime collection operations while rejecting symbolic key types", c do
    assert {:ok, %{families: families}} =
             OrderedCollectionModels.audit(
               c.audit.functions,
               c.models,
               c.t,
               c.refs,
               @crates,
               :runtime
             )

    assert Enum.sort(families) == ~w(map set)
    model = Enum.find_value(c.models, fn {_, m} -> if m[:ordered_method] == "insert", do: m end)
    owner = hd(c.audit.functions)

    args = %{
      "regions" => [%{"Body" => 0}],
      "types" => [%{"Scalar" => %{"Integer" => %{"Unsigned" => "U32"}}}],
      "trait_refs" => [],
      "const_generics" => []
    }

    f =
      Map.put(owner, "body", %{
        "Regular" => %{"kind" => %{"Fun" => model.function["def_id"]}, "generics" => args}
      })

    assert {:error, _, message} =
             OrderedCollectionModels.audit([f], c.models, c.t, c.refs, @crates, :pure)

    assert message =~ "concrete u64"
  end

  defp hydrate(doc) do
    doc
    |> LLBCJson.restore_type_references!(doc)
    |> LLBCJson.restore_trait_references!(doc)
    |> LLBCJson.restore_constant_references!(doc)
    |> LLBCJson.restore_spans!(doc)
  end

  defp update_declaration(doc, key, id, change) do
    doc = hydrate(doc)

    update_in(
      doc,
      ["translated", key],
      &Enum.map(&1, fn d -> if d && d["def_id"] == id, do: change.(d), else: d end)
    )
  end
end
