defmodule Lynx.Rust.ScalarCallbackTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LLBC, ResultModels}
  @snapshot Path.expand("../../fixtures/rustler/scalar_callback.json", __DIR__)

  setup do
    document = JSON.decode!(File.read!(@snapshot))
    translated = document["translated"]
    functions = Enum.reject(translated["fun_decls"], &is_nil/1)
    refs = LLBC.type_references!(document)
    models = CallModels.resolve(functions, translated, refs, [])
    closure = Enum.find(translated["type_decls"], &(&1 && match?(%{"Closure" => _}, &1["src"])))
    %{translated: translated, functions: functions, refs: refs, models: models, closure: closure}
  end

  test "retains actual scalar environment, callback body and compiler destructor evidence", ctx do
    assert {:ok, dependencies} =
             ResultModels.audit(ctx.functions, ctx.models, ctx.translated, ctx.refs)

    body = get_in(ctx.closure, ["src", "Closure", "info", "closure_body", "id"])
    assert Enum.any?(dependencies, fn {_, ids} -> ids == [body] end)
    assert Enum.any?(ctx.models, fn {_, model} -> model[:callback] == :compiler_fn_once end)
    assert %{"Struct" => [%{"ty" => type}]} = ctx.closure["kind"]

    assert CallModels.expand(type, ctx.refs) ==
             %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}
  end

  test "rejects mutable, generic, owned aggregate and malformed captures", ctx do
    for field <- [
          %{"ty" => %{"Ref" => ["Static", %{"Scalar" => "Bool"}, "Mut"]}},
          %{"ty" => %{"TypeVar" => %{"Free" => 0}}},
          %{"ty" => %{"Adt" => %{"id" => 999_999, "builtin" => nil, "generics" => %{}}}},
          %{}
        ] do
      translated = replace_closure(ctx, put_in(ctx.closure, ["kind", "Struct"], [field]))

      assert {:error, _, message} =
               ResultModels.audit(ctx.functions, ctx.models, translated, ctx.refs)

      assert message =~ "empty or scalar captures"
    end
  end

  test "an absent compiler NoopDestruct witness cannot be inferred from scalar fields", ctx do
    translated = rewrite(ctx.translated)
    functions = rewrite(ctx.functions)

    assert {:error, _, message} =
             ResultModels.audit(functions, ctx.models, translated, ctx.refs)

    assert message =~ "NoopDestruct"
  end

  test "scalar fields cannot replace the extracted callback implementation", ctx do
    id = get_in(ctx.closure, ["src", "Closure", "info", "closure_body", "id"])
    functions = Enum.reject(ctx.functions, &(&1["def_id"] == id))

    assert {:error, _, message} =
             ResultModels.audit(functions, ctx.models, ctx.translated, ctx.refs)

    assert message =~ "extracted compiler FnOnce"
  end

  defp replace_closure(ctx, closure) do
    Map.update!(ctx.translated, "type_decls", fn types ->
      Enum.map(types, fn
        %{"def_id" => id} = type -> if id == closure["def_id"], do: closure, else: type
        type -> type
      end)
    end)
  end

  defp rewrite(%{"builtin_data" => "NoopDestruct"} = node),
    do: %{node | "builtin_data" => "OtherDestruct"}

  defp rewrite(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, rewrite(v)} end)
  defp rewrite(list) when is_list(list), do: Enum.map(list, &rewrite/1)
  defp rewrite(value), do: value
end
