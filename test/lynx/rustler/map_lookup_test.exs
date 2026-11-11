defmodule Lynx.Rustler.MapLookupTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{FormatModels, LLBC}
  alias Lynx.Rustler.EncoderModels
  @snapshot Path.expand("../../fixtures/rustler/error_drop.json", __DIR__)

  setup do
    snapshot = JSON.decode!(File.read!(@snapshot))
    document = snapshot["document"]

    %{
      getter: snapshot["map_get"],
      debug: snapshot["debug"],
      translated: document["translated"],
      refs: LLBC.type_references!(document)
    }
  end

  test "map lookup retains its Encoder dictionary and by-value key restriction", ctx do
    assert %{
             lean: "Lynx.Rustler.Decoding.mapGet",
             can_fail: true,
             encoder_copy_key: true,
             encoder_slots: 1,
             encoder_regions: 1
           } = EncoderModels.resolve(ctx.getter, ctx.translated, ctx.refs)

    [term, key] = ctx.getter["signature"]["inputs"]

    for changed <- [
          put_in(ctx.getter, ["signature", "abi"], "C"),
          put_in(ctx.getter, ["signature", "is_unsafe"], true),
          put_in(ctx.getter, ["signature", "inputs"], [key, term]),
          put_in(ctx.getter, ["signature", "output"], term),
          put_in(ctx.getter, ["generics", "trait_clauses"], []),
          put_in(ctx.getter, ["generics", "outlives"], [%{}]),
          Map.put(ctx.getter, "body", %{"Structured" => %{}})
        ],
        do: assert(is_nil(EncoderModels.resolve(changed, ctx.translated, ctx.refs)))
  end

  test "rejects owned key destruction before accepting an Encoder call", ctx do
    getter = ctx.getter
    model = EncoderModels.resolve(getter, ctx.translated, ctx.refs)

    function =
      Enum.find(
        ctx.translated["fun_decls"],
        &(&1 &&
            Enum.any?(&1["item_meta"]["name"], fn n ->
              n == %{"Ident" => ["try_decode_field", 0]}
            end))
      )

    owned =
      Enum.find(
        ctx.translated["type_decls"],
        &(&1 && List.last(&1["item_meta"]["name"]) == %{"Ident" => ["OrderedMap", 0]})
      )

    self = %{
      "Adt" => %{
        "id" => owned["def_id"],
        "builtin" => nil,
        "generics" => %{
          "types" => [],
          "regions" => [],
          "const_generics" => [],
          "trait_refs" => []
        }
      }
    }

    changed = owned_key(function, getter["def_id"], self)
    refute function == changed

    assert {:error, _, message} =
             EncoderModels.audit(
               [changed],
               %{getter["def_id"] => model},
               ctx.translated,
               ctx.refs
             )

    assert message =~ "owned key destruction is unsupported"
  end

  defp owned_key(%{"Regular" => %{"kind" => %{"Fun" => id}} = call}, id, self),
    do: %{"Regular" => put_in(call, ["generics", "types"], [self])}

  defp owned_key(map, id, self) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, owned_key(v, id, self)} end)

  defp owned_key(list, id, self) when is_list(list), do: Enum.map(list, &owned_key(&1, id, self))
  defp owned_key(value, _, _), do: value

  test "Debug argument validation does not substitute a Display dictionary", ctx do
    assert %{bounded_formatting: true, display_trait: trait} =
             FormatModels.resolve(ctx.debug, ctx.translated, ctx.refs)

    assert is_integer(trait)

    for changed <- [
          put_in(ctx.debug, ["signature", "abi"], "C"),
          put_in(ctx.debug, ["signature", "is_unsafe"], true),
          put_in(ctx.debug, ["generics", "trait_clauses"], []),
          put_in(ctx.debug, ["generics", "outlives"], [])
        ],
        do: assert(is_nil(FormatModels.resolve(changed, ctx.translated, ctx.refs)))

    translated =
      update_in(ctx.translated, ["trait_decls", Access.at(trait), "item_meta", "name"], fn _ ->
        Enum.map(~w(core fmt Display), &%{"Ident" => [&1, 0]})
      end)

    assert is_nil(FormatModels.resolve(ctx.debug, translated, ctx.refs))
  end
end
