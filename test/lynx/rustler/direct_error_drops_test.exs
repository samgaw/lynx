defmodule Lynx.Rustler.DirectErrorDropsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{DropModels, LLBC}
  alias Lynx.Rustler.ErrorDrops
  @snapshot Path.expand("../../fixtures/rustler/direct_error_drop.json", __DIR__)
  @error Enum.map(~w(rustler error Error), &%{"Ident" => [&1, 0]})
  @crates ~w(experiment_nif experiment_core experiment_analysis)

  setup do
    %{"document" => doc, "layout" => layout} = JSON.decode!(File.read!(@snapshot))
    functions = doc["translated"]["fun_decls"]

    caller =
      Enum.find(
        functions,
        &(&1 && List.last(&1["item_meta"]["name"]) == %{"Ident" => ["discard_direct", 0]})
      )

    [drop] = drops(caller["body"])
    id = drop["fn_ptr"]["kind"]["Fun"]
    glue = Enum.find(functions, &(&1 && &1["def_id"] == id))

    %{
      doc: doc,
      layout: layout,
      caller: caller,
      drop: drop,
      glue: glue,
      refs: LLBC.type_references!(doc)
    }
  end

  test "direct Error cleanup retains an explicit partial model and compiler identity", ctx do
    assert %{id: id} =
             DropModels.validate_opaque_glue!(
               ctx.drop,
               ctx.caller,
               ctx.doc["translated"],
               ctx.refs,
               @error
             )

    assert id == ctx.glue["def_id"]
    assert ErrorDrops.needed?(ctx.doc, @crates)
    {lowered, proof} = ErrorDrops.lower!(ctx.doc, ctx.layout, @crates)

    assert Enum.any?(
             proof.sites,
             &(&1.caller == ctx.caller["def_id"] and &1.mode == :error and &1.compiler_drop == id)
           )

    assert Enum.any?(ErrorDrops.models!(lowered, proof), fn {_, model} ->
             model.lean == "Lynx.Rustler.Decoding.dropDecoderError" and
               not model.implementation_verified and
               String.contains?(model.label, "boxed errors exhaust")
           end)

    changed =
      Enum.find(lowered["translated"]["fun_decls"], &(&1 && &1["def_id"] == ctx.caller["def_id"]))

    assert drops(changed["body"]) == []
  end

  test "rejects mismatched glue bodies, signatures, methods and lifetime scopes", ctx do
    for glue <- [
          put_in(ctx.glue, ["body"], %{"Structured" => %{}}),
          put_in(ctx.glue, ["signature", "is_unsafe"], false),
          put_in(ctx.glue, ["signature", "abi"], "C"),
          put_in(ctx.glue, ["src", "TraitImpl", "reuses_default"], true),
          put_in(ctx.glue, ["signature", "output"], %{"Scalar" => "Bool"})
        ] do
      t =
        update_in(
          ctx.doc["translated"],
          ["fun_decls"],
          &Enum.map(&1, fn
            %{"def_id" => id} = f -> if(id == glue["def_id"], do: glue, else: f)
            f -> f
          end)
        )

      assert_raise ArgumentError, ~r/opaque external drop glue/, fn ->
        DropModels.validate_opaque_glue!(ctx.drop, ctx.caller, t, ctx.refs, @error)
      end
    end

    for region <- [
          %{"Body" => -1},
          %{"Body" => 999_999},
          %{"Var" => %{"Free" => 999}},
          %{"Var" => %{"Bound" => [0, 0]}}
        ] do
      drop = put_in(ctx.drop, ["fn_ptr", "generics", "regions"], [region])

      assert_raise ArgumentError, ~r/opaque external drop glue/, fn ->
        DropModels.validate_opaque_glue!(
          drop,
          ctx.caller,
          ctx.doc["translated"],
          ctx.refs,
          @error
        )
      end
    end

    impl = ctx.glue["src"]["TraitImpl"]["impl_ref"]["id"]

    t =
      update_in(
        ctx.doc["translated"],
        ["trait_impls"],
        &Enum.map(&1, fn
          %{"def_id" => ^impl} = row -> %{row | "methods" => []}
          row -> row
        end)
      )

    assert_raise ArgumentError, ~r/opaque external drop glue/, fn ->
      DropModels.validate_opaque_glue!(ctx.drop, ctx.caller, t, ctx.refs, @error)
    end
  end

  defp drops(%{"Drop" => drop} = node), do: [drop | Enum.flat_map(Map.values(node), &drops/1)]
  defp drops(map) when is_map(map), do: Enum.flat_map(Map.values(map), &drops/1)
  defp drops(list) when is_list(list), do: Enum.flat_map(list, &drops/1)
  defp drops(_), do: []
end
