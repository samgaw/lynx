defmodule Lynx.Rustler.ErrorConstructorsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.LLBC
  alias Lynx.Rustler.{DecoderModels, ErrorConstructors}
  @snapshot Path.expand("../../fixtures/rustler/error_constructor.json", __DIR__)
  @crates ["experiment_nif", "experiment_core", "experiment_analysis", "experiment_unrelated"]

  setup do
    @snapshot
    |> File.read!()
    |> JSON.decode!()
    |> Map.new(fn {key, value} -> {String.to_existing_atom(key), value} end)
  end

  test "normalizes only a compiled zero-field foreign constructor without erasing drops", ctx do
    assert ErrorConstructors.needed?(ctx.document, @crates)
    {lowered, proof} = ErrorConstructors.lower!(ctx.document, ctx.layout, @crates)
    assert [%{caller: caller, statement: statement}] = proof.sites
    assert is_integer(caller) and is_integer(statement)
    assert drops(lowered) == drops(ctx.document)
    assert lowered["translated"]["type_decls"] == ctx.document["translated"]["type_decls"]
    assert proof.variant["name"] == "BadArg"
    assert proof.variant["fields"] == []
    assert Enum.at(lowered["translated"]["fun_decls"], proof.function_id) == proof.declaration

    assert %{implementation_verified: false, can_fail: false, lean: "Lynx.Rustler.badArgOutcome"} =
             ErrorConstructors.models!(lowered, proof)[proof.function_id]

    refute ErrorConstructors.needed?(lowered, @crates)

    functions =
      Enum.filter(lowered["translated"]["fun_decls"], fn f ->
        f && f["item_meta"]["is_local"]
      end)

    assert {:ok, %{}} =
             DecoderModels.audit(functions, lowered["translated"], LLBC.type_references!(lowered))
  end

  test "rejects wrong enum identity, payload arity and inconsistent variant IDs", ctx do
    error = error_type(ctx.layout)
    [badarg | rest] = error["kind"]["Enum"]

    for changed <- [
          put_in(error, ["item_meta", "name"], [%{"Ident" => ["other", 0]}]),
          put_in(error, ["kind", "Enum"], [%{badarg | "fields" => [%{}]} | rest]),
          put_in(error, ["kind", "Enum"], [%{badarg | "id" => 3} | rest]),
          put_in(error, ["kind", "Enum"], [%{badarg | "id" => -5} | rest]),
          put_in(error, ["item_meta", "has_errors"], true)
        ] do
      layout =
        update_in(ctx.layout, ["translated", "type_decls"], fn types ->
          Enum.map(types, fn t -> if t == error, do: changed, else: t end)
        end)

      assert_raise ArgumentError, fn ->
        ErrorConstructors.lower!(ctx.document, layout, @crates)
      end
    end

    ambiguous =
      update_in(ctx.layout, ["translated", "type_decls"], &(&1 ++ [%{error | "def_id" => 999}]))

    assert_raise ArgumentError, ~r/ambiguous compiled Rustler Error/, fn ->
      ErrorConstructors.lower!(ctx.document, ambiguous, @crates)
    end

    assert_raise ArgumentError, ~r/first-party Error semantics/, fn ->
      ErrorConstructors.lower!(ctx.document, ctx.layout, ["rustler" | @crates])
    end
  end

  test "requires the exact primitive declaration and original destination type", ctx do
    {lowered, proof} = ErrorConstructors.lower!(ctx.document, ctx.layout, @crates)

    changed =
      update_in(
        lowered,
        ["translated", "fun_decls"],
        &List.replace_at(&1, proof.function_id, nil)
      )

    assert_raise ArgumentError, ~r/inconsistent validated Rustler BadArg/, fn ->
      ErrorConstructors.models!(changed, proof)
    end

    id = error_type(ctx.document)["def_id"]
    changed = poison(ctx.document, id)
    refute changed == ctx.document

    assert_raise CompileError, ~r/inconsistent Rustler BadArg constructor type/, fn ->
      ErrorConstructors.lower!(changed, ctx.layout, @crates)
    end
  end

  defp error_type(doc),
    do:
      Enum.find(doc["translated"]["type_decls"], fn t ->
        t && t["item_meta"]["name"] == Enum.map(~w(rustler error Error), &%{"Ident" => [&1, 0]})
      end)

  defp drops(%{"Drop" => _} = map), do: 1 + Enum.sum(Enum.map(Map.values(map), &drops/1))
  defp drops(map) when is_map(map), do: Enum.sum(Enum.map(Map.values(map), &drops/1))
  defp drops(list) when is_list(list), do: Enum.sum(Enum.map(list, &drops/1))
  defp drops(_), do: 0

  defp poison(
         %{
           "Assign" => [place, %{"Aggregate" => [%{"Adt" => [%{"id" => id}, 0, nil]}, []]} = rhs]
         },
         id
       ),
       do: %{"Assign" => [%{place | "ty" => %{"Scalar" => "Bool"}}, rhs]}

  defp poison(map, id) when is_map(map), do: Map.new(map, fn {k, v} -> {k, poison(v, id)} end)
  defp poison(list, id) when is_list(list), do: Enum.map(list, &poison(&1, id))
  defp poison(value, _), do: value
end
