defmodule Lynx.Rust.VectorIndexTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CollectionModels, IndexModels}
  @snapshot Path.expand("../../fixtures/rustler/vector_index.json", __DIR__)

  setup do
    %{"function" => function, "translated" => translated, "call" => call} =
      JSON.decode!(File.read!(@snapshot))

    %{function: function, translated: translated, call: call}
  end

  test "retains the compiled generic Index wrapper and its allocator audit", ctx do
    assert %{lean: "Aeneas.Std.alloc.vec.Vec.index", builtin: true, vec_owned_method: "index"} =
             model = IndexModels.resolve(ctx.function, ctx.translated, %{})

    assert :ok =
             CollectionModels.audit(
               [%{"body" => ctx.call}],
               %{ctx.function["def_id"] => model},
               ctx.translated,
               %{}
             )
  end

  test "rejects altered compiler signatures and implementation dictionaries", ctx do
    for function <- [
          put_in(ctx.function, ["signature", "is_unsafe"], true),
          put_in(ctx.function, ["signature", "abi"], "C"),
          put_in(ctx.function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(ctx.function, ["src", "TraitImpl", "reuses_default"], true),
          put_in(ctx.function, ["src", "TraitImpl", "trait_ref", "id"], 999_999),
          put_in(ctx.function, ["generics", "trait_clauses"], []),
          put_in(ctx.function, ["generics", "outlives"], [])
        ] do
      refute IndexModels.resolve(function, ctx.translated, %{})
    end

    [impl] = ctx.translated["trait_impls"]

    for changed <- [
          Map.put(impl, "is_negative", true),
          Map.put(impl, "is_unsafe", true),
          Map.put(impl, "methods", []),
          Map.put(impl, "methods", impl["methods"] ++ impl["methods"])
        ] do
      translated = %{ctx.translated | "trait_impls" => [changed]}
      refute IndexModels.resolve(ctx.function, translated, %{})
    end
  end

  test "unknown and missing allocators cannot use the standard vector model", ctx do
    model = IndexModels.resolve(ctx.function, ctx.translated, %{})
    models = %{ctx.function["def_id"] => model}
    types = ctx.call["Regular"]["generics"]["types"]

    for changed <- [
          List.replace_at(types, 2, %{"TypeVar" => %{"Free" => 0}}),
          List.replace_at(types, 2, %{"Scalar" => "Bool"}),
          List.delete_at(types, 2)
        ] do
      call = put_in(ctx.call, ["Regular", "generics", "types"], changed)

      assert {:error, _, message} =
               CollectionModels.audit([%{"body" => call}], models, ctx.translated, %{})

      assert message =~ "only the standard Global allocator"
    end

    translated = %{ctx.translated | "type_decls" => []}

    assert {:error, _, _} =
             CollectionModels.audit([%{"body" => ctx.call}], models, translated, %{})
  end

  test "rejects vector dispatch without captured SliceIndex method evidence", ctx do
    model = IndexModels.resolve(ctx.function, ctx.translated, %{})
    caller = %{"def_id" => 999, "body" => %{"Call" => %{"call" => %{"func" => ctx.call}}}}

    assert {:error, _, message} =
             IndexModels.audit([caller], %{ctx.function["def_id"] => model}, ctx.translated, %{})

    assert message =~ "missing or unsupported SliceIndex"
  end
end
