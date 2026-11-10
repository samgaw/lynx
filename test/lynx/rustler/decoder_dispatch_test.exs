defmodule Lynx.Rustler.DecoderDispatchTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LLBC}
  alias Lynx.Rustler.DecoderDispatch

  setup do
    document =
      Path.expand("../../fixtures/rustler/decoder_dispatch.json", __DIR__)
      |> File.read!()
      |> JSON.decode!()

    translated = document["translated"]

    functions =
      Enum.filter(translated["fun_decls"], fn f ->
        f && match?([%{"Ident" => ["experiment_nif", 0]} | _], f["item_meta"]["name"])
      end)

    refs = LLBC.type_references!(document)
    external = Enum.reject(Enum.reject(translated["fun_decls"], &is_nil/1), &(&1 in functions))
    models = CallModels.resolve(external, translated, refs, [:rustler_decoders])
    decoder = Enum.find(functions, &match?(%{"TraitImpl" => _}, &1["src"]))

    %{
      document: document,
      translated: translated,
      functions: functions,
      refs: refs,
      models: models,
      decoder: decoder
    }
  end

  test "closes primitive and first-party dictionaries and admits only the checked clause call",
       ctx do
    assert {:ok, %{dependencies: dependencies, calls: calls}} =
             DecoderDispatch.audit(ctx.functions, ctx.models, ctx.translated, ctx.refs)

    root =
      Enum.find(
        ctx.functions,
        &(List.last(&1["item_meta"]["name"]) == %{"Ident" => ["decode_flag_via", 0]})
      )

    assert ctx.decoder["def_id"] in dependencies[root["def_id"]]
    assert Enum.count(Map.values(calls), &(&1 != [])) == 1
  end

  test "rejects a missing first-party body or missing primitive model", ctx do
    missing = Enum.reject(ctx.functions, &(&1["def_id"] == ctx.decoder["def_id"]))

    assert {:error, _, message} =
             DecoderDispatch.audit(missing, ctx.models, ctx.translated, ctx.refs)

    assert message =~ "Decoder dictionary dependency"
    assert {:error, _, _} = DecoderDispatch.audit(ctx.functions, %{}, ctx.translated, ctx.refs)
  end

  test "rejects inconsistent implementation, method identity and concrete Self", ctx do
    impl_id = ctx.decoder["src"]["TraitImpl"]["impl_ref"]["id"]
    impl = Enum.find(ctx.translated["trait_impls"], &(&1 && &1["def_id"] == impl_id))

    for bad <- [
          %{impl | "methods" => []},
          put_in(impl, ["impl_trait", "generics", "types"], [%{"Scalar" => "Bool"}]),
          %{impl | "is_unsafe" => true}
        ] do
      t = %{
        ctx.translated
        | "trait_impls" =>
            Enum.map(ctx.translated["trait_impls"], &if(&1 == impl, do: bad, else: &1))
      }

      assert {:error, _, _} = DecoderDispatch.audit(ctx.functions, ctx.models, t, ctx.refs)
    end

    bad = put_in(ctx.decoder, ["src", "TraitImpl", "item_id"], 1)
    functions = Enum.map(ctx.functions, &if(&1 == ctx.decoder, do: bad, else: &1))

    t = %{
      ctx.translated
      | "fun_decls" =>
          Enum.map(ctx.translated["fun_decls"], &if(&1 == ctx.decoder, do: bad, else: &1))
    }

    assert {:error, _, _} = DecoderDispatch.audit(functions, ctx.models, t, ctx.refs)
  end

  test "does not grant a call-site allowance to another trait method slot", ctx do
    change = fn change, value ->
      case value do
        %{"Regular" => %{"kind" => %{"Trait" => [reference, 0]}} = regular} ->
          %{"Regular" => %{regular | "kind" => %{"Trait" => [reference, 1]}}}

        map when is_map(map) ->
          Map.new(map, fn {key, value} -> {key, change.(change, value)} end)

        list when is_list(list) ->
          Enum.map(list, &change.(change, &1))

        value ->
          value
      end
    end

    functions = change.(change, ctx.functions)

    assert {:ok, %{calls: calls}} =
             DecoderDispatch.audit(functions, ctx.models, ctx.translated, ctx.refs)

    assert Enum.all?(Map.values(calls), &(&1 == []))
  end
end
