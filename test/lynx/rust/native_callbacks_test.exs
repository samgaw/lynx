defmodule Lynx.Rust.NativeCallbacksTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LLBC, OptionModels, ResultModels}
  @snapshot Path.expand("../../fixtures/rustler/tagged_decoder_models.json", __DIR__)

  setup do
    document = JSON.decode!(File.read!(@snapshot))
    translated = document["translated"]
    refs = LLBC.type_references!(document)
    functions = Enum.reject(translated["fun_decls"], &is_nil/1)
    pure = CallModels.resolve(functions, translated, refs, [:rustler_decoders])
    native = CallModels.resolve(functions, translated, refs, [:rustler_decoders], :runtime)
    callbacks = Map.filter(native, fn {_, model} -> model[:native_callback] end)
    %{document: document, callbacks: callbacks, native: native, pure: pure}
  end

  test "selects native callbacks without changing pure models or their capture audit", ctx do
    assert map_size(ctx.callbacks) == 1

    for {id, model} <- ctx.callbacks do
      assert model.lean in ["Lynx.NativeCallbacks.andThen", "Lynx.NativeCallbacks.mapErr"]
      assert model.lift and not model.builtin
      assert model.function == ctx.pure[id].function
      assert model.fn_once_trait == ctx.pure[id].fn_once_trait
      assert model.destruct_trait == ctx.pure[id].destruct_trait
    end

    assert OptionModels.scope(%{external_calls: ctx.callbacks}, "Scoped").external_calls ==
             ctx.callbacks

    refute Enum.any?(ctx.pure, fn {_, model} -> model[:native_callback] end)
  end

  test "aliases preserve implementation bodies, signatures, IDs and original Rust names", ctx do
    {lowered, ids} = ResultModels.lower_native_names!(ctx.document, ctx.callbacks)
    assert Enum.sort(ids) == Enum.sort(Map.keys(ctx.callbacks))

    for {original, changed} <-
          Enum.zip(ctx.document["translated"]["fun_decls"], lowered["translated"]["fun_decls"]) do
      if original && original["def_id"] in ids do
        assert put_in(changed, ["item_meta", "name"], original["item_meta"]["name"]) == original
      else
        assert changed == original
      end
    end

    assert %{"trait_decls" => [%{"extract_name" => "Lynx.NativeCallbacks.FnOnce"}]} =
             ResultModels.external_names(%{external_calls: ctx.callbacks}, :runtime)

    assert ResultModels.external_names(%{external_calls: ctx.callbacks}, :pure) == %{}
  end

  test "refuses changed opaque callback identities before backend aliasing", ctx do
    [{id, model} | _] = Map.to_list(ctx.callbacks)

    for changed <- [
          put_in(model.function, ["signature", "is_unsafe"], true),
          Map.put(model.function, "src", "Changed"),
          Map.put(model.function, "body", %{"Structured" => %{}})
        ] do
      document =
        update_in(ctx.document, ["translated", "fun_decls"], fn functions ->
          Enum.map(functions, fn function ->
            if function && function["def_id"] == id, do: changed, else: function
          end)
        end)

      assert_raise ArgumentError, ~r/original audited opaque declaration/, fn ->
        ResultModels.lower_native_names!(document, ctx.callbacks)
      end
    end
  end

  test "rejects callback trait aliases colliding with compiler declarations", ctx do
    [trait | _] = Enum.reject(ctx.document["translated"]["trait_decls"], &is_nil/1)

    collision =
      trait
      |> Map.put("def_id", 999)
      |> put_in(["item_meta", "name"], Enum.map(~w(lynx_native FnOnce), &%{"Ident" => [&1, 0]}))

    document = update_in(ctx.document, ["translated", "trait_decls"], &(&1 ++ [collision]))

    assert_raise ArgumentError, ~r/trait alias collides/, fn ->
      ResultModels.lower_native_names!(document, ctx.callbacks)
    end
  end
end
