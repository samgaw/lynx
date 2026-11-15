defmodule Lynx.Rust.VectorExtensionsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CollectionModels, VectorExtensions}
  @snapshot Path.expand("../../fixtures/rustler/vector_extension.json", __DIR__)

  setup do
    %{"translated" => translated, "arguments" => args} = JSON.decode!(File.read!(@snapshot))
    [extend, clone] = translated["fun_decls"]
    %{translated: translated, args: args, extend: extend, clone: clone}
  end

  test "resolves the actual standard extension and byte Clone definitions", ctx do
    assert %{
             vec_owned_method: "extend_from_slice",
             can_fail: true,
             native_cutoff_only: true,
             keep_params: [true, false]
           } = VectorExtensions.resolve(ctx.extend, ctx.translated, %{})

    assert %{lean: "Aeneas.Std.core.clone.impls.CloneU8.clone", can_fail: false, lift: false} =
             VectorExtensions.resolve(ctx.clone, ctx.translated, %{})

    assert VectorExtensions.valid_call?(ctx.args, ctx.translated, %{})
    assert :ok = audit(ctx.args, ctx.translated, ctx.extend)
  end

  test "requires the exact byte Clone dictionary and Global allocator", ctx do
    for args <- [
          put_in(ctx.args, ["types", Access.at(0)], %{"Scalar" => "Bool"}),
          put_in(ctx.args, ["types", Access.at(1), "Adt", "id"], 7),
          put_in(ctx.args, ["trait_refs"], []),
          put_in(
            ctx.args,
            [
              "trait_refs",
              Access.at(0),
              "skip_binder",
              "Value",
              Access.at(1),
              "trait_decl_ref",
              "id"
            ],
            99
          ),
          put_in(
            ctx.args,
            [
              "trait_refs",
              Access.at(0),
              "skip_binder",
              "Value",
              Access.at(1),
              "kind",
              "TraitImpl",
              "id"
            ],
            99
          )
        ] do
      assert {:error, _, message} = audit(args, ctx.translated, ctx.extend)
      assert message =~ "audited standard Clone<u8>"
    end
  end

  test "rejects changed, missing or first-party Clone behavior", ctx do
    for clone <- [
          put_in(ctx.clone, ["signature", "is_unsafe"], true),
          put_in(ctx.clone, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(ctx.clone, ["src", "TraitImpl", "reuses_default"], true),
          put_in(ctx.clone, ["item_meta", "name"], [%{"Ident" => ["user_clone", 0]}]),
          Map.put(ctx.clone, "body", %{"Structured" => %{}})
        ] do
      translated = put_in(ctx.translated, ["fun_decls", Access.at(1)], clone)
      refute VectorExtensions.resolve(clone, translated, %{})
      refute VectorExtensions.valid_call?(ctx.args, translated, %{})
    end

    refute VectorExtensions.valid_call?(
             ctx.args,
             put_in(ctx.translated, ["fun_decls"], [ctx.extend]),
             %{}
           )

    changed =
      put_in(
        ctx.translated,
        ["trait_impls", Access.at(0), "methods", Access.at(0), "skip_binder", "id"],
        99
      )

    refute VectorExtensions.valid_call?(ctx.args, changed, %{})
  end

  test "rejects changed extension ABI, lifetime bounds and trait identity", ctx do
    for extend <- [
          put_in(ctx.extend, ["signature", "is_variadic"], true),
          put_in(ctx.extend, ["signature", "inputs", Access.at(1), "Ref", Access.at(2)], "Mut"),
          put_in(ctx.extend, ["generics", "outlives"], []),
          put_in(ctx.extend, ["generics", "trait_clauses"], []),
          put_in(ctx.extend, ["item_meta", "name", Access.at(3), "Ident", Access.at(0)], "extend")
        ],
        do: refute(VectorExtensions.resolve(extend, ctx.translated, %{}))

    for {path, value} <- [
          {["item_meta", "lang_item"], nil},
          {["item_meta", "name"], [%{"Ident" => ["Clone", 0]}]},
          {["is_unsafe"], true}
        ] do
      translated = put_in(ctx.translated, ["trait_decls", Access.at(0)] ++ path, value)
      refute VectorExtensions.resolve(ctx.extend, translated, %{})
      refute VectorExtensions.valid_call?(ctx.args, translated, %{})
    end
  end

  defp audit(args, translated, extend) do
    model = VectorExtensions.resolve(extend, translated, %{})

    function = %{
      "def_id" => 90,
      "body" => %{"Regular" => %{"kind" => %{"Fun" => extend["def_id"]}, "generics" => args}}
    }

    CollectionModels.audit([function], %{extend["def_id"] => model}, translated, %{})
  end
end
