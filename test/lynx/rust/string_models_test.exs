defmodule Lynx.Rust.StringModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.StringModels
  @snapshot Path.expand("../../fixtures/rustler/string_views.json", __DIR__)

  test "admits compiler-linked shared text views using existing Lean definitions" do
    %{"functions" => functions, "translated" => translated} = snapshot()
    assert length(functions) == 3

    for f <- functions do
      method = List.last(f["item_meta"]["name"])["Ident"] |> hd()

      assert %{builtin: false, implementation_verified: false, status: :modelled} =
               Lynx.Rust.CallModels.resolve([f], translated, %{}, [])[f["def_id"]]

      assert %{lean: lean} = StringModels.resolve(f, translated, %{})

      assert lean ==
               %{
                 "as_bytes" => "id",
                 "len" => "Aeneas.Std.Slice.len",
                 "is_empty" => "Aeneas.Std.core.slice.Slice.is_empty"
               }[method]
    end
  end

  test "rejects altered method identity, lifetime, mutability and function signature" do
    %{"functions" => functions, "translated" => translated} = snapshot()

    for f <- functions do
      [input] = f["signature"]["inputs"]
      [region, str, _] = input["Ref"]

      for changed <- [
            Map.put(f, "body", %{"Structured" => %{}}),
            Map.put(f, "src", %{"TraitImpl" => %{}}),
            put_in(f, ["signature", "is_unsafe"], true),
            put_in(f, ["signature", "is_variadic"], true),
            put_in(f, ["signature", "abi"], "C"),
            put_in(f, ["signature", "inputs"], [%{"Ref" => [region, str, "Mut"]}]),
            put_in(f, ["signature", "inputs"], [
              %{"Ref" => [%{"Var" => %{"Free" => 1}}, str, "Shared"]}
            ]),
            put_in(f, ["signature", "output"], input),
            put_in(f, ["generics", "regions"], []),
            put_in(f, ["generics", "trait_clauses"], [%{}]),
            put_in(f, ["item_meta", "name"], [%{"Ident" => ["str", 0]}])
          ] do
        refute StringModels.resolve(changed, translated, %{})
      end
    end
  end

  test "checks the actual builtin str representation and parent type" do
    %{"functions" => functions, "translated" => %{"type_decls" => [str]} = translated} =
      snapshot()

    for changed <- [
          Map.put(str, "src", "Normal"),
          Map.put(str, "kind", "Opaque"),
          put_in(str, ["kind", "Struct"], []),
          put_in(str, ["kind", "Struct"], [%{"name" => "_0", "ty" => %{"Scalar" => "Bool"}}]),
          put_in(str, ["item_meta", "name"], [%{"Ident" => ["Str", 0]}]),
          put_in(str, ["generics", "types"], [%{"index" => 0}])
        ],
        f <- functions do
      refute StringModels.resolve(f, Map.put(translated, "type_decls", [changed]), %{})
    end

    for f <- functions do
      [core, str, %{"Impl" => %{"Ty" => parent}}, method] = f["item_meta"]["name"]

      for changed <- [
            Map.put(parent, "skip_binder", %{"Scalar" => "Bool"}),
            put_in(parent, ["params", "types"], [%{"index" => 0}]),
            Map.put(parent, "kind", "TraitImpl")
          ] do
        f = put_in(f, ["item_meta", "name"], [core, str, %{"Impl" => %{"Ty" => changed}}, method])
        refute StringModels.resolve(f, translated, %{})
      end
    end
  end

  defp snapshot, do: JSON.decode!(File.read!(@snapshot))
end
