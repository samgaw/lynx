defmodule Lynx.Rust.SliceIndexModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, IndexModels, LLBC, SliceModels}
  @snapshot Path.expand("../../fixtures/rustler/slice_index.json", __DIR__)

  setup do
    document = File.read!(@snapshot) |> JSON.decode!()
    translated = document["translated"]
    refs = LLBC.type_references!(document)
    functions = Enum.reject(translated["fun_decls"], &is_nil/1)
    models = CallModels.resolve(functions, translated, refs, [])

    wrapper =
      Enum.find_value(models, fn {_, model} -> if model[:slice_index_method] == 4, do: model end)

    range =
      Enum.find_value(models, fn {_, model} ->
        if model.lean == "Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.index",
          do: model
      end)

    caller =
      Enum.find(functions, fn f ->
        List.last(f["item_meta"]["name"]) == %{"Ident" => ["indexed_prefix", 0]}
      end)

    array =
      Enum.find(functions, fn f ->
        List.last(f["item_meta"]["name"]) == %{"Ident" => ["array_window_length", 0]} and
          hd(f["item_meta"]["name"]) == %{"Ident" => ["experiment_core", 0]}
      end)

    %{
      array: array,
      translated: translated,
      refs: refs,
      wrapper: wrapper,
      range: range,
      caller: caller,
      models: models
    }
  end

  test "recognizes the compiled slice-index wrapper and bounds-panic primitive", ctx do
    assert %{
             rust_name: "core::slice::index::{core::ops::index::Index<[@T], @I, @O>}::index",
             lean: "Aeneas.Std.core.slice.index.Slice.index",
             slice_index_method: 4
           } = ctx.wrapper

    assert %{builtin: true, can_fail: true, implementation_verified: false, status: :modelled} =
             ctx.range

    assert {:ok, dependencies} =
             IndexModels.audit([ctx.caller], ctx.models, ctx.translated, ctx.refs)

    assert ctx.range.definition_id in dependencies[ctx.caller["def_id"]]
  end

  test "rejects missing delegated implementations", ctx do
    assert {:error, _, message} =
             IndexModels.audit(
               [ctx.caller],
               Map.delete(ctx.models, ctx.range.definition_id),
               ctx.translated,
               ctx.refs
             )

    assert message =~ "missing or unsupported SliceIndex"
  end

  test "checks actual range method identity and safe shared signature", ctx do
    for changed <- [
          put_in(ctx.range.function, ["signature", "is_unsafe"], true),
          put_in(ctx.range.function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(ctx.range.function, ["src", "TraitImpl", "item_id"], 0),
          put_in(ctx.range.function, ["src", "TraitImpl", "reuses_default"], true)
        ] do
      refute SliceModels.resolve(changed, ctx.translated, ctx.refs)
    end
  end

  test "does not accept the former shortened wrapper path or a foreign trait identity", ctx do
    f = ctx.wrapper.function
    shortened = List.delete_at(f["item_meta"]["name"], 2)

    refute IndexModels.resolve(
             put_in(f, ["item_meta", "name"], shortened),
             ctx.translated,
             ctx.refs
           )

    refute IndexModels.resolve(
             put_in(f, ["src", "TraitImpl", "trait_ref", "id"], 999_999),
             ctx.translated,
             ctx.refs
           )
  end

  test "tracks array delegation and rejects a missing intermediate dictionary", ctx do
    assert {:ok, dependencies} =
             IndexModels.audit([ctx.array], ctx.models, ctx.translated, ctx.refs)

    assert ctx.wrapper.definition_id in dependencies[ctx.array["def_id"]]

    assert {:error, _, message} =
             IndexModels.audit(
               [ctx.array],
               Map.delete(ctx.models, ctx.wrapper.definition_id),
               ctx.translated,
               ctx.refs
             )

    assert message =~ "missing or unsupported delegated standard Index"
  end
end
