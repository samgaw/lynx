defmodule Lynx.Rust.SharedCallbackTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, LLBC, ResultModels}
  @fixtures Path.expand("../../fixtures/rustler", __DIR__)

  for kind <- ~w(scalar slice) do
    @tag capture: kind
    test "checks the actual shared #{kind} environment and callback implementation", ctx do
      ctx = snapshot(ctx.capture)
      assert %{"Struct" => [%{"ty" => type}]} = ctx.closure["kind"]

      assert %{"Ref" => [%{"Var" => %{"Free" => 0}}, _, "Shared"]} =
               CallModels.expand(type, ctx.refs)

      assert [%{"index" => 0}] =
               Enum.map(ctx.closure["generics"]["regions"], &Map.take(&1, ["index"]))

      assert {:ok, dependencies} = audit(ctx, ctx.translated)
      body = get_in(ctx.closure, ["src", "Closure", "info", "closure_body", "id"])
      assert Enum.any?(dependencies, fn {_, ids} -> ids == [body] end)
    end

    @tag capture: kind
    test "rejects unscoped lifetime IDs in shared #{kind} captures", ctx do
      ctx = snapshot(ctx.capture)
      [%{"ty" => type} = field] = ctx.closure["kind"]["Struct"]
      %{"Ref" => [_, data, "Shared"]} = CallModels.expand(type, ctx.refs)

      for region <- [
            %{"Var" => %{"Free" => -1}},
            %{"Var" => %{"Free" => 1}},
            %{"Var" => %{"Bound" => [0, 0]}},
            %{"Body" => 0},
            "Erased"
          ] do
        field = Map.put(field, "ty", %{"Ref" => [region, data, "Shared"]})
        assert {:error, _, message} = audit(ctx, replace_field(ctx, field))
        assert message =~ "shared references to scalar/slice values"
      end
    end

    @tag capture: kind
    test "rejects mutable and unsupported data behind shared #{kind} captures", ctx do
      ctx = snapshot(ctx.capture)
      scalar = %{"Scalar" => "Bool"}
      region = %{"Var" => %{"Free" => 0}}

      for type <- [
            %{"Ref" => [region, scalar, "Mut"]},
            %{"Ref" => [region, %{"Ref" => [region, scalar, "Mut"]}, "Shared"]},
            %{"Ref" => [region, %{"TypeVar" => %{"Free" => 0}}, "Shared"]},
            %{
              "Ref" => [
                region,
                %{"Slice" => [%{"Ref" => [region, scalar, "Shared"]}, nil]},
                "Shared"
              ]
            },
            %{"Slice" => [scalar, nil]}
          ] do
        assert {:error, _, _} = audit(ctx, replace_field(ctx, %{"ty" => type}))
      end
    end

    @tag capture: kind
    test "shared #{kind} references do not replace compiler destruction or closure provenance",
         ctx do
      ctx = snapshot(ctx.capture)
      assert {:error, _, _} = audit(ctx, rewrite(ctx.translated))

      changed =
        Map.update!(ctx.translated, "type_decls", fn types ->
          Enum.map(types, fn type ->
            if type && type["def_id"] == ctx.closure["def_id"],
              do: Map.put(type, "src", "Normal"),
              else: type
          end)
        end)

      assert {:error, _, _} = audit(ctx, changed)
    end
  end

  defp snapshot(kind) do
    document = JSON.decode!(File.read!(Path.join(@fixtures, "shared_#{kind}_callback.json")))
    translated = document["translated"]
    refs = LLBC.type_references!(document)
    functions = Enum.reject(translated["fun_decls"], &is_nil/1)
    models = CallModels.resolve(functions, translated, refs, [])
    closure = Enum.find(translated["type_decls"], &(&1 && match?(%{"Closure" => _}, &1["src"])))
    %{translated: translated, refs: refs, models: models, closure: closure}
  end

  defp audit(ctx, translated),
    do:
      ResultModels.audit(
        Enum.reject(translated["fun_decls"], &is_nil/1),
        ctx.models,
        translated,
        ctx.refs
      )

  defp replace_field(ctx, field) do
    Map.update!(ctx.translated, "type_decls", fn types ->
      Enum.map(types, fn type ->
        if type && type["def_id"] == ctx.closure["def_id"],
          do: put_in(type, ["kind", "Struct"], [field]),
          else: type
      end)
    end)
  end

  defp rewrite(%{"builtin_data" => "NoopDestruct"} = node),
    do: %{node | "builtin_data" => "OtherDestruct"}

  defp rewrite(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, rewrite(v)} end)
  defp rewrite(list) when is_list(list), do: Enum.map(list, &rewrite/1)
  defp rewrite(value), do: value
end
