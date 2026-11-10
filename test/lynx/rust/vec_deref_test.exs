defmodule Lynx.Rust.VecDerefTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.CallModels

  setup do
    file = Path.expand("../../fixtures/rust_collections/vec_deref.json", __DIR__)
    %{"function" => function, "translated" => translated} = file |> File.read!() |> JSON.decode!()
    %{function: function, translated: translated}
  end

  test "recognizes the actual standard Vec shared Deref and filters the allocator parameter",
       ctx do
    assert %{
             26 => %{
               lean: "Aeneas.Std.alloc.vec.Vec.deref",
               keep_params: [true, false],
               builtin: true,
               can_fail: false,
               lift: false,
               implementation_verified: false
             }
           } =
             CallModels.resolve([ctx.function], ctx.translated, %{}, [])
  end

  test "rejects different trait, unsafe methods, mismatched identities and altered lifetimes",
       ctx do
    for function <- [
          put_in(ctx.function, ["signature", "abi"], "C"),
          put_in(ctx.function, ["signature", "is_unsafe"], true),
          put_in(ctx.function, ["src", "TraitImpl", "item_id"], 1),
          put_in(ctx.function, ["src", "TraitImpl", "reuses_default"], true),
          put_in(ctx.function, ["generics", "outlives"], []),
          put_in(ctx.function, ["signature", "output"], %{"Scalar" => "Bool"})
        ] do
      assert CallModels.resolve([function], ctx.translated, %{}, []) == %{}
    end

    [impl] = ctx.translated["trait_impls"]
    [trait] = ctx.translated["trait_decls"]

    for translated <- [
          %{ctx.translated | "trait_impls" => [%{impl | "is_unsafe" => true}]},
          %{ctx.translated | "trait_impls" => [%{impl | "methods" => []}]},
          %{ctx.translated | "trait_impls" => [%{impl | "types" => []}]},
          %{ctx.translated | "trait_decls" => [put_in(trait, ["item_meta", "name"], [])]},
          %{ctx.translated | "trait_decls" => [%{trait | "methods" => []}]}
        ] do
      assert CallModels.resolve([ctx.function], translated, %{}, []) == %{}
    end
  end
end
