defmodule Lynx.Rust.SliceRangeModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.SliceModels
  @snapshot Path.expand("../../fixtures/rustler/slice_ranges.json", __DIR__)

  for kind <- ~w(Range RangeFrom) do
    @tag range: kind
    test "admits the compiled #{kind} safe getter as an external model", ctx do
      {function, translated, _} = snapshot(ctx.range)
      assert %{builtin: true, lean: lean} = SliceModels.resolve(function, translated, %{})
      assert lean == "Aeneas.Std.core.slice.index.SliceIndex#{ctx.range}UsizeSlice.get"
    end

    @tag range: kind
    test "checks the actual #{kind} definition and ordered field types", ctx do
      {function, translated, range} = snapshot(ctx.range)
      fields = range["kind"]["Struct"]
      range_id = range["def_id"]

      changes = [
        Map.put(range, "kind", "Opaque"),
        put_in(range, ["item_meta", "name"], [%{"Ident" => [ctx.range, 0]}]),
        put_in(range, ["generics", "types"], []),
        put_in(range, ["kind", "Struct"], []),
        put_in(range, ["kind", "Struct"], fields ++ fields),
        put_in(
          range,
          ["kind", "Struct"],
          Enum.map(fields, &Map.put(&1, "ty", %{"Scalar" => "Bool"}))
        ),
        put_in(range, ["kind", "Struct"], Enum.map(fields, &Map.put(&1, "name", "limit")))
      ]

      changes =
        if length(fields) > 1,
          do: [put_in(range, ["kind", "Struct"], Enum.reverse(fields)) | changes],
          else: changes

      for changed <- changes do
        translated =
          Map.update!(
            translated,
            "type_decls",
            &Enum.map(&1, fn
              %{"def_id" => ^range_id} -> changed
              row -> row
            end)
          )

        refute SliceModels.resolve(function, translated, %{})
      end
    end

    @tag range: kind
    test "rejects inconsistent #{kind} method identities and signatures", ctx do
      {function, translated, _} = snapshot(ctx.range)

      for changed <- [
            put_in(function, ["signature", "abi"], "C"),
            put_in(function, ["signature", "is_unsafe"], true),
            put_in(function, ["signature", "output"], %{"Scalar" => "Bool"}),
            put_in(function, ["src", "TraitImpl", "item_id"], 1),
            put_in(function, ["src", "TraitImpl", "reuses_default"], true),
            put_in(function, ["src", "TraitImpl", "trait_ref", "id"], 999_999)
          ] do
        refute SliceModels.resolve(changed, translated, %{})
      end

      impl_id = function["src"]["TraitImpl"]["impl_ref"]["id"]
      impl = Enum.find(translated["trait_impls"], &(&1["def_id"] == impl_id))

      for changed <- [
            Map.put(impl, "methods", []),
            Map.put(impl, "is_negative", true)
          ] do
        id = changed["def_id"]

        translated =
          Map.update!(
            translated,
            "trait_impls",
            &Enum.map(&1, fn
              %{"def_id" => ^id} -> changed
              row -> row
            end)
          )

        # Each call is checked against its own implementation, not any other
        # valid range dictionary which happens to exist in the same module.
        refute SliceModels.resolve(function, translated, %{})
      end
    end
  end

  defp snapshot(kind) do
    %{"functions" => functions, "translated" => translated} = JSON.decode!(File.read!(@snapshot))

    function =
      Enum.find(functions, fn function ->
        case SliceModels.resolve(function, translated, %{}) do
          %{lean: lean} -> lean == "Aeneas.Std.core.slice.index.SliceIndex#{kind}UsizeSlice.get"
          _ -> false
        end
      end)

    %{"Adt" => %{"id" => id}} = hd(function["signature"]["inputs"])
    range = Enum.find(translated["type_decls"], &(&1["def_id"] == id))
    {function, translated, range}
  end
end
