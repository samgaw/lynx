defmodule Lynx.Rustler.CopyModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rustler.CopyModels
  @snapshot Path.expand("../../fixtures/rustler/copy_models.json", __DIR__)

  setup do
    JSON.decode!(File.read!(@snapshot))
    |> then(fn %{"functions" => functions, "translated" => translated} ->
      %{functions: functions, translated: translated}
    end)
  end

  test "validates real Term and Atom Copy dictionaries and distinct RustM clones", ctx do
    assert [
             %{lean: "Lynx.Rustler.copyTermHandle", can_fail: true, lift: true},
             %{lean: "Lynx.Rustler.copyAtomHandle", can_fail: true, lift: true}
           ] = Enum.map(ctx.functions, &CopyModels.resolve(&1, ctx.translated, %{}))
  end

  test "rejects altered ABI, ownership, output and method identity", ctx do
    for function <- ctx.functions,
        changed <- [
          put_in(function, ["signature", "abi"], "C"),
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(function, ["signature", "inputs"], []),
          put_in(function, ["src", "TraitImpl", "item_id"], 1),
          put_in(function, ["generics", "outlives"], [%{}]),
          Map.put(function, "def_id", -1)
        ] do
      assert CopyModels.resolve(changed, ctx.translated, %{}) == nil
    end
  end

  test "rejects missing and inconsistent Copy and Clone evidence", ctx do
    for function <- ctx.functions do
      for translated <- [
            %{ctx.translated | "trait_impls" => []},
            %{ctx.translated | "trait_decls" => []},
            update_in(ctx.translated, ["trait_impls"], fn impls ->
              Enum.map(impls, &Map.put(&1, "is_unsafe", true))
            end),
            update_in(ctx.translated, ["trait_impls"], fn impls ->
              Enum.map(impls, &Map.put(&1, "is_negative", true))
            end),
            update_in(ctx.translated, ["trait_impls"], fn impls ->
              Enum.map(impls, &put_in(&1, ["generics", "outlives"], [%{}]))
            end),
            update_in(ctx.translated, ["trait_impls"], fn impls ->
              Enum.map(impls, &Map.put(&1, "methods", []))
            end)
          ] do
        assert CopyModels.resolve(function, translated, %{}) == nil
      end
    end
  end
end
