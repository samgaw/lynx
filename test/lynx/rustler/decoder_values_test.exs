defmodule Lynx.Rustler.DecoderValuesTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{ResourceModels}
  alias Lynx.Rustler.DecoderValues
  @snapshot Path.expand("../../fixtures/rustler/decoder_value.json", __DIR__)

  setup do
    type = JSON.decode!(File.read!(@snapshot))

    audit = %{
      translated: %{"type_decls" => [type]},
      references: %{},
      first_party: ["experiment_nif"]
    }

    %{type: type, audit: audit, id: type["def_id"]}
  end

  test "admits the compiled scalar decoder payload with actual no-drop evidence", ctx do
    DecoderValues.validate!(ctx.id, ctx.audit)
  end

  test "requires definite compiler evidence and actual first-party fields", ctx do
    [field] = ctx.type["kind"]["Struct"]

    for type <- [
          Map.put(ctx.type, "needs_drop", nil),
          Map.put(ctx.type, "needs_drop", true),
          Map.put(ctx.type, "kind", "Opaque"),
          put_in(ctx.type, ["item_meta", "has_errors"], true),
          put_in(ctx.type, ["generics", "trait_clauses"], [%{}]),
          put_in(ctx.type, ["item_meta", "name"], [%{"Ident" => ["foreign", 0]}]),
          put_in(ctx.type, ["kind", "Struct"], [Map.put(field, "ty", %{"Ref" => []})])
        ] do
      audit = put_in(ctx.audit, [:translated, "type_decls"], [type])

      assert_raise CompileError, ~r/runtime Rustler Decoder payload/, fn ->
        DecoderValues.validate!(ctx.id, audit)
      end
    end
  end

  test "no-drop metadata cannot hide foreign or recursive native ownership", ctx do
    [field] = ctx.type["kind"]["Struct"]

    for id <- [ctx.id, 91] do
      reference = %{
        "Adt" => %{"id" => id, "builtin" => nil, "generics" => ResourceModels.args([])}
      }

      changed = put_in(ctx.type, ["kind", "Struct"], [Map.put(field, "ty", reference)])
      native = %{"def_id" => 91, "kind" => "Opaque", "needs_drop" => false}
      audit = put_in(ctx.audit, [:translated, "type_decls"], [changed, native])

      assert_raise CompileError, ~r/native owners, opaque fields/, fn ->
        DecoderValues.validate!(ctx.id, audit)
      end
    end
  end

  test "recursively checks tuple and enum fields", ctx do
    [field] = ctx.type["kind"]["Struct"]
    tuple = %{"Adt" => %{"builtin" => "Tuple", "generics" => ResourceModels.args([field["ty"]])}}
    type = put_in(ctx.type, ["kind"], %{"Enum" => [%{"fields" => [Map.put(field, "ty", tuple)]}]})
    DecoderValues.validate!(ctx.id, put_in(ctx.audit, [:translated, "type_decls"], [type]))
  end
end
