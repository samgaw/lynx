defmodule Lynx.Rust.SliceIndexDispatchTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, IndexModels, LLBC, SliceModels}
  @snapshot Path.expand("../../fixtures/rustler/borrowed_prefix.json", __DIR__)

  setup do
    document = JSON.decode!(File.read!(@snapshot))
    audit = LLBC.audit!(document, ["prefix_core", "prefix_analysis"])

    {id, model} =
      Enum.find(audit.external_calls, fn {_, model} ->
        model.lean == "Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.get"
      end)

    %{document: document, audit: audit, model: model, id: id}
  end

  test "reports the actual delegated range operation as a model", ctx do
    assert %{builtin: true, implementation_verified: false, status: :modelled} = ctx.model
    assert Enum.any?(ctx.audit.trait_dependencies, fn {_, methods} -> ctx.id in methods end)
    assert Enum.any?(LLBC.dependencies(ctx.audit), fn {_, methods} -> ctx.id in methods end)
  end

  test "checks nominal range identity, field type and method signature", ctx do
    translated = ctx.audit.translated
    refs = ctx.audit.references

    %{"Adt" => %{"id" => id}} =
      hd(CallModels.expand(ctx.model.function["signature"]["inputs"], refs))

    range = Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id))

    for changed <- [
          put_in(range, ["item_meta", "name"], [%{"Ident" => ["RangeTo", 0]}]),
          Map.put(range, "kind", "Opaque"),
          put_in(range, ["kind", "Struct"], [%{"name" => "end", "ty" => %{"Scalar" => "Bool"}}])
        ] do
      translated =
        Map.update!(
          translated,
          "type_decls",
          &Enum.map(&1, fn
            %{"def_id" => ^id} -> changed
            type -> type
          end)
        )

      refute SliceModels.resolve(ctx.model.function, translated, refs)
    end

    for changed <- [
          put_in(ctx.model.function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(ctx.model.function, ["src", "TraitImpl", "reuses_default"], true),
          put_in(ctx.model.function, ["src", "TraitImpl", "item_id"], 1)
        ] do
      refute SliceModels.resolve(changed, ctx.audit.translated, refs)
    end
  end

  test "rejects missing delegated implementations before extraction", ctx do
    models = Map.delete(ctx.audit.available_external_calls, ctx.id)

    assert {:error, _, message} =
             IndexModels.audit(
               ctx.audit.functions,
               models,
               ctx.audit.translated,
               ctx.audit.references
             )

    assert message =~ "missing or unsupported SliceIndex"
  end

  test "only the exact standard usize get dictionary is nonpanicking" do
    args = fn types ->
      %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}
    end

    byte = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}
    usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
    variable = %{"TypeVar" => %{"Free" => 0}}
    slice = fn element -> %{"Slice" => [element, nil]} end

    dictionary = %{
      "regions" => [],
      "outlives" => [],
      "skip_binder" => %{
        "Value" => [
          40,
          %{
            "kind" => %{"TraitImpl" => %{"id" => 4, "generics" => args.([byte])}},
            "trait_decl_ref" => %{"id" => 3, "generics" => args.([usize, slice.(byte), byte])}
          }
        ]
      }
    }

    call = %{
      "func" => %{
        "Regular" => %{
          "kind" => %{"Fun" => 1},
          "generics" => %{
            args.([byte, usize, byte])
            | "regions" => ["Erased"],
              "trait_refs" => [dictionary]
          }
        }
      }
    }

    impl = %{
      "def_id" => 4,
      "impl_trait" => %{"id" => 3, "generics" => args.([usize, slice.(variable), variable])},
      "methods" => [%{"kind" => %{"TraitMethod" => [3, 0]}, "skip_binder" => %{"id" => 7}}]
    }

    context = %{translated: %{"trait_impls" => [impl]}, references: %{}}

    wrapper = %{
      lean: "Aeneas.Std.core.slice.Slice.get",
      builtin: true,
      slice_index_method: 0,
      can_fail: true
    }

    leaf = %{lean: "Aeneas.Std.core.slice.index.Usize.get", builtin: true, can_fail: false}
    models = %{1 => wrapper, 7 => leaf}
    assert IndexModels.nonpanicking_get?(call, models, context)

    for changed <- [
          Map.delete(models, 7),
          put_in(models, [7, :can_fail], true),
          put_in(models, [7, :lean], "unproved.get"),
          put_in(models, [1, :slice_index_method], 4),
          put_in(models, [7, :builtin], false)
        ] do
      refute IndexModels.nonpanicking_get?(call, changed, context)
    end

    refute IndexModels.nonpanicking_get?(
             call,
             models,
             put_in(context, [:translated, "trait_impls"], [])
           )

    refute IndexModels.nonpanicking_get?(
             put_in(call, ["func", "Regular", "generics", "trait_refs"], []),
             models,
             context
           )
  end
end
