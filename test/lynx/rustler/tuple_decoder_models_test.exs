defmodule Lynx.Rustler.TupleDecoderModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rustler.DecoderModels

  setup do
    snapshot = Path.expand("../../fixtures/rustler/decoder_tuple.json", __DIR__)

    %{"function" => function, "translated" => translated} =
      snapshot |> File.read!() |> JSON.decode!()

    %{function: function, translated: translated}
  end

  test "admits actual tuple FFI identity and ordered vector result", ctx do
    assert %{lean: "Lynx.Rustler.Decoding.getTuple", can_fail: true, lift: false} =
             DecoderModels.resolve(ctx.function, ctx.translated, %{})
  end

  test "rejects altered ABI, lifetimes, result and vector layout", ctx do
    for f <- [
          put_in(ctx.function, ["signature", "abi"], "C"),
          put_in(ctx.function, ["signature", "is_unsafe"], true),
          put_in(ctx.function, ["generics", "regions"], []),
          put_in(ctx.function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(ctx.function, ["body"], %{})
        ] do
      assert DecoderModels.resolve(f, ctx.translated, %{}) == nil
    end

    types =
      Enum.map(ctx.translated["type_decls"], fn d ->
        if List.last(d["item_meta"]["name"]) == %{"Ident" => ["Vec", 0]},
          do: put_in(d, ["generics", "types"], []),
          else: d
      end)

    assert DecoderModels.resolve(ctx.function, %{ctx.translated | "type_decls" => types}, %{}) ==
             nil
  end
end
