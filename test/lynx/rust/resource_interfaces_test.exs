defmodule Lynx.Rust.ResourceInterfacesTest do
  use ExUnit.Case, async: true

  alias Lynx.Rust.{
    CallModels,
    LLBC,
    NativeDrops,
    ResourceAudit,
    ResourceInterfaces,
    ResourceModels
  }

  @fixture Path.expand("../../fixtures/rustler/ordered_resources.json", __DIR__)

  setup do
    doc = @fixture |> File.read!() |> JSON.decode!()
    t = doc["translated"]
    refs = LLBC.type_references!(t)

    trait =
      Enum.find(
        t["trait_decls"],
        &(&1 && &1["item_meta"]["name"] == path(~w(rustler resource traits Resource)))
      )

    impl = Enum.find(t["trait_impls"], &(&1 && &1["impl_trait"]["id"] == trait["def_id"]))
    [payload] = CallModels.expand(impl["impl_trait"]["generics"]["types"], refs)
    dict = hd(hd(impl["consts"])["generics"]["trait_refs"])

    functions =
      Enum.filter(t["fun_decls"], fn f ->
        f &&
          hd(f["item_meta"]["name"])["Ident"] in Enum.map(
            ~w(experiment_core experiment_analysis experiment_nif),
            &[&1, 0]
          )
      end)

    %{
      doc: doc,
      t: t,
      refs: refs,
      trait: trait,
      impl: impl,
      payload: payload,
      dictionary: dict,
      audit: %{functions: functions, external_calls: %{0 => %{native_resource_type: 0}}}
    }
  end

  test "admits materialized foreign default callbacks with their actual resource dictionary", c do
    assert Enum.all?(c.impl["methods"], &is_map/1)
    assert payload?(c.t, c)

    assert %{"body" => %{"Structured" => _}} =
             Lynx.Rust.NativeOwnedDrops.function_for(c.payload, c.t, c.refs)

    {projected, record} = ResourceInterfaces.project!(c.doc, c.audit)
    assert %{omitted_functions: [_, _], omitted_types: [_, _, _]} = record

    assert Enum.all?(c.audit.functions, fn f ->
             Enum.any?(projected["translated"]["fun_decls"], &(&1 && &1["def_id"] == f["def_id"]))
           end)
  end

  test "rejects callback overrides and mismatched inherited method forwarding", c do
    method = hd(c.impl["methods"])
    id = method["skip_binder"]["id"]

    for change <- [
          &Map.put(&1, "src", "Normal"),
          &put_in(&1, ["src", "TraitDefault", "item_id"], 1),
          &put_in(&1, ["signature", "abi"], "C"),
          &put_in(&1, ["signature", "is_unsafe"], true)
        ] do
      changed = update(c.t, "fun_decls", id, change)
      refute payload?(changed, c)
    end

    changed =
      update(c.t, "trait_impls", c.impl["def_id"], fn impl ->
        put_in(impl, ["methods", Access.at(0), "skip_binder", "generics", "regions"], [])
      end)

    refute payload?(changed, c)
  end

  test "never omits an observed callback body or trait call", c do
    callback = hd(c.impl["methods"])["skip_binder"]["id"]
    source = hd(c.audit.functions)

    for body <- [
          %{
            "Regular" => %{"kind" => %{"Fun" => callback}, "generics" => ResourceModels.args([])}
          },
          %{"Trait" => [c.dictionary["skip_binder"], 0]}
        ] do
      hydrated =
        c.doc
        |> Lynx.Rust.LLBCJson.restore_type_references!(c.doc)
        |> Lynx.Rust.LLBCJson.restore_trait_references!(c.doc)
        |> Lynx.Rust.LLBCJson.restore_constant_references!(c.doc)

      changed =
        update(hydrated["translated"], "fun_decls", source["def_id"], &Map.put(&1, "body", body))

      assert_raise ArgumentError, ~r/observed omitted resource callback/, fn ->
        ResourceInterfaces.project!(%{c.doc | "translated" => changed}, c.audit)
      end
    end
  end

  test "mutex disposal retains the concrete u64 key and allocator restrictions", c do
    type = Enum.find(c.t["type_decls"], &(&1 && &1["def_id"] == c.payload["Adt"]["id"]))
    [field | _] = type["kind"]["Struct"]
    mutex = CallModels.expand(field["ty"], c.refs)
    [map] = mutex["Adt"]["generics"]["types"]
    assert NativeDrops.supported_mutex_payload?(mutex, c.t, c.refs)

    for position <- [0, 2] do
      wrong_map =
        put_in(map, ["Adt", "generics", "types", Access.at(position)], %{
          "Scalar" => %{"Integer" => %{"Unsigned" => "U32"}}
        })

      wrong_mutex = put_in(mutex, ["Adt", "generics", "types"], [wrong_map])
      refute NativeDrops.supported_mutex_payload?(wrong_mutex, c.t, c.refs)
    end
  end

  test "retains a foreign callback type referenced by another declaration", c do
    env =
      Enum.find(c.t["type_decls"], &(&1 && &1["item_meta"]["name"] == path(~w(rustler env Env))))

    id = env["def_id"]
    next = 1 + Enum.max(for d <- c.t["type_decls"], d, do: d["def_id"])

    reference = %{
      "Adt" => %{
        "id" => id,
        "builtin" => nil,
        "generics" => ResourceModels.args([], [], [%{"Var" => %{"Free" => 0}}])
      }
    }

    view =
      env
      |> Map.put("def_id", next)
      |> put_in(["item_meta", "name"], path(~w(experiment_core EnvView)))
      |> Map.put("kind", %{
        "Struct" => [%{"name" => "env", "is_positional" => false, "ty" => reference}]
      })

    doc = update_in(c.doc, ["translated", "type_decls"], &(&1 ++ [view]))
    {projected, record} = ResourceInterfaces.project!(doc, c.audit)
    refute id in record.omitted_types

    assert Enum.any?(
             projected["translated"]["type_decls"],
             &match?(%{"def_id" => ^id, "kind" => "Opaque"}, &1)
           )
  end

  defp payload?(t, c),
    do:
      ResourceAudit.payload?(
        c.payload,
        c.dictionary,
        c.trait["def_id"],
        t,
        LLBC.type_references!(t),
        ResourceModels.trait_references(t)
      )

  defp update(t, key, id, change),
    do:
      Map.update!(
        t,
        key,
        &Enum.map(&1, fn d -> if d && d["def_id"] == id, do: change.(d), else: d end)
      )

  defp path(names), do: Enum.map(names, &%{"Ident" => [&1, 0]})
end
