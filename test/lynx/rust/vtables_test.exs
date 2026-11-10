defmodule Lynx.Rust.VTablesTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{BoxModels, VTables}
  @snapshot Path.expand("../../fixtures/rust/vtable.json", __DIR__)
  setup do
    data = @snapshot |> File.read!() |> JSON.decode!()
    refs = Map.new(data["refs"], fn [id, type] -> {id, type} end)
    translated = data["translated"]
    functions = Enum.filter(translated["fun_decls"], &(&1 && &1["item_meta"]["is_local"]))

    %{
      globals: data["globals"],
      translated: translated,
      refs: refs,
      functions: functions,
      translation: data["translation"]
    }
  end

  test "validates metadata and retains actual methods as dependencies", ctx do
    {tables, functions, deps} = audit(ctx)
    assert map_size(tables) == 1
    [table] = Map.values(tables)
    assert %{methods: [method], shims: [drop, slot]} = table["lynx_vtable"]
    assert Enum.any?(functions, &(&1["def_id"] == method))
    refute Enum.any?(functions, &(&1["def_id"] in [drop, slot]))
    assert Enum.any?(deps, fn {_, methods} -> method in methods end)
    assert %{"modelled" => true, "inlined" => true} = VTables.link!(table, ctx.translation)

    assert_raise ArgumentError, ~r/extracted Rust vtable dictionary/, fn ->
      VTables.link!(table, %{ctx.translation | "trait_impls" => []})
    end
  end

  test "rejects vtable identity, size and method changes", ctx do
    [global] = ctx.globals

    assert_raise ArgumentError, ~r/duplicate LLBC constant identity/, fn ->
      audit(%{ctx | globals: [global, global]})
    end

    for changed <- [
          put_in(global, ["src", "VTableInstance", "impl_ref", "id"], 999),
          put_in(global, ["item_meta", "has_errors"], true),
          put_in(
            global,
            ["value", "Value", Access.at(1), Access.at(0), "Adt", Access.at(1), Access.at(0)],
            %{"Value" => [999, [%{"Integer" => %{"Unsigned" => ["Usize", "1"]}}, %{}]]}
          )
        ] do
      assert_raise ArgumentError, ~r/compiler vtable metadata/, fn ->
        audit(%{ctx | globals: [changed]})
      end
    end
  end

  test "rejects changed shims and an observable destructor", ctx do
    {tables, _, _} = audit(ctx)
    [table] = Map.values(tables)
    %{shims: [drop, slot]} = table["lynx_vtable"]

    for {id, change} <- [
          {drop,
           fn f ->
             update_in(
               f,
               ["body", "Structured", "body", "statements"],
               &(&1 ++ [%{"kind" => %{"Call" => %{}}}])
             )
           end},
          {slot, fn f -> put_in(f, ["src"], "Normal") end}
        ] do
      translated =
        update_in(
          ctx.translated,
          ["fun_decls"],
          &Enum.map(&1, fn f -> if f && f["def_id"] == id, do: change.(f), else: f end)
        )

      assert_raise ArgumentError, ~r/compiler vtable metadata/, fn ->
        audit(%{ctx | translated: translated})
      end
    end
  end

  test "Box allocation requires the actual diagnostic identity and bounded generic signature",
       ctx do
    box =
      Enum.find(
        ctx.translated["fun_decls"],
        &(&1 && &1["item_meta"]["diagnostic_item"] == "box_new")
      )

    models = Lynx.Rust.CallModels.resolve([box], ctx.translated, ctx.refs, [])

    assert %{builtin: true, can_fail: false, implementation_verified: false, status: :modelled} =
             models[box["def_id"]]

    for changed <- [
          put_in(box, ["signature", "abi"], "C"),
          put_in(box, ["item_meta", "diagnostic_item"], nil),
          put_in(box, ["generics", "const_generics"], [%{}])
        ] do
      assert BoxModels.resolve(changed, ctx.translated, ctx.refs) == nil
    end
  end

  defp audit(ctx), do: VTables.audit!(ctx.globals, ctx.functions, ctx.translated, ctx.refs)
end
