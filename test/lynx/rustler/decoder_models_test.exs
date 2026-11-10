defmodule Lynx.Rustler.DecoderModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rustler.DecoderModels
  @snapshot Path.expand("../../fixtures/rustler/decoder_u64.json", __DIR__)

  setup do
    %{"function" => function, "translated" => translated} =
      @snapshot |> File.read!() |> JSON.decode!()

    %{function: function, translated: translated}
  end

  test "admits the compiled primitive Decoder identity and exact bounded signature", ctx do
    assert %{lean: "Lynx.Rustler.Decoding.u64", can_fail: true, lift: false} =
             DecoderModels.resolve(ctx.function, ctx.translated, %{})
  end

  test "rejects altered method identity, ABI, result type and generic bounds", ctx do
    for function <- [
          put_in(ctx.function, ["signature", "abi"], "C"),
          put_in(ctx.function, ["signature", "is_unsafe"], true),
          put_in(ctx.function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(ctx.function, ["src", "TraitImpl", "item_id"], 1),
          put_in(ctx.function, ["body"], %{}),
          put_in(ctx.function, ["generics", "outlives"], [%{}])
        ] do
      assert DecoderModels.resolve(function, ctx.translated, %{}) == nil
    end

    [trait] = ctx.translated["trait_decls"]
    [impl] = ctx.translated["trait_impls"]

    for translated <- [
          %{ctx.translated | "trait_decls" => [put_in(trait, ["generics", "outlives"], [])]},
          %{ctx.translated | "trait_impls" => [%{impl | "is_negative" => true}]},
          %{ctx.translated | "trait_impls" => [%{impl | "is_unsafe" => true}]},
          %{ctx.translated | "trait_impls" => [put_in(impl, ["methods"], [])]}
        ] do
      assert DecoderModels.resolve(ctx.function, translated, %{}) == nil
    end
  end

  test "rejects opaque Error construction, discriminants and nested payload access", ctx do
    error =
      Enum.find(ctx.translated["type_decls"], &(&1["kind"] == "Opaque" and &1["def_id"] == 8))

    id = error["def_id"]

    type = %{
      "Adt" => %{
        "id" => id,
        "builtin" => nil,
        "generics" => %{
          "regions" => [],
          "types" => [],
          "const_generics" => [],
          "trait_refs" => []
        }
      }
    }

    place = %{"ty" => type, "kind" => %{"Local" => 0}}
    field = %{"kind" => %{"Projection" => [place, %{"Field" => [0, 0]}]}}

    for body <- [
          %{"Aggregate" => [%{"Adt" => [%{"id" => id}, 0, []]}, []]},
          %{"Discriminant" => place},
          %{"Match" => [place, []]},
          %{"nested" => field},
          %{"kind" => %{"Projection" => [field, %{"Field" => [0, 0]}]}}
        ] do
      function = %{"body" => body}
      assert {:error, ^function, message} = DecoderModels.audit([function], ctx.translated, %{})
      assert message =~ "only opaque error forwarding"
    end

    assert {:ok, %{}} =
             DecoderModels.audit([%{"body" => %{"Move" => place}}], ctx.translated, %{})
  end
end
