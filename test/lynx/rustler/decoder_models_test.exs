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

  test "runtime dictionaries retain primitive identity through the runtime interpreter", ctx do
    pure = DecoderModels.resolve(ctx.function, ctx.translated, %{})

    assert %{
             lean: "Lynx.Rustler.NativeDecoding.u64",
             native_cutoff_only: true,
             can_fail: true,
             lift: false
           } = native = DecoderModels.for_execution(pure, :runtime)

    assert Map.drop(native, [:lean, :native_cutoff_only]) == Map.drop(pure, [:lean])
    audit = %{external_calls: %{0 => pure}, decoder_dispatch: %{calls: %{}}}

    assert %{
             "trait_decls" => [
               %{
                 "extract_name" => "Lynx.Rustler.NativeDecoder",
                 "constructor" => "Lynx.Rustler.NativeDecoder.mk"
               }
             ]
           } =
             DecoderModels.external_names(audit, :runtime)

    assert %{"trait_decls" => [%{"extract_name" => "Lynx.Rustler.Decoder"}]} =
             DecoderModels.external_names(audit)
  end

  test "catalogues fixed-width scalar dictionaries and rejects altered signatures", ctx do
    for name <- ~w(bool i8 i16 i32 i64 u8 u16 u32 u64) do
      type =
        if name == "bool",
          do: %{"Scalar" => "Bool"},
          else: %{
            "Scalar" => %{
              "Integer" => %{
                if(String.starts_with?(name, "i"), do: "Signed", else: "Unsigned") =>
                  String.upcase(name)
              }
            }
          }

      replace = fn value ->
        replace_scalar(value, type)
      end

      function = replace.(ctx.function)
      translated = replace.(ctx.translated)

      assert %{lean: lean, decoder_trait: 4} =
               model = DecoderModels.resolve(function, translated, %{})

      assert lean == "Lynx.Rustler.Decoding.#{name}"

      assert %{lean: native, native_cutoff_only: true} =
               DecoderModels.for_execution(model, :runtime)

      assert native == "Lynx.Rustler.NativeDecoding.#{name}"

      assert DecoderModels.resolve(put_in(function, ["signature", "inputs"], []), translated, %{}) ==
               nil
    end
  end

  test "runtime lifts reject uncatalogued decoder operations" do
    assert DecoderModels.for_execution(nil, :runtime) == nil

    assert_raise ArgumentError, ~r/unsupported runtime Rustler decoder primitive/, fn ->
      DecoderModels.for_execution(%{lean: "Lynx.Rustler.Decoding.unqualified"}, :runtime)
    end
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

  defp replace_scalar(%{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}, type), do: type

  defp replace_scalar(map, type) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, replace_scalar(v, type)} end)

  defp replace_scalar(list, type) when is_list(list),
    do: Enum.map(list, &replace_scalar(&1, type))

  defp replace_scalar(value, _type), do: value
end
