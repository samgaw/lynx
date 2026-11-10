defmodule Lynx.Rustler.CopyVectorDropTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{DropModels, LLBC}

  setup do
    document =
      Path.expand("../../fixtures/rustler/copy_vector_drop.json", __DIR__)
      |> File.read!()
      |> JSON.decode!()

    translated = document["translated"]

    function =
      Enum.find(
        translated["fun_decls"],
        &(&1 &&
            List.last(&1["item_meta"]["name"]) == %{"Ident" => ["tuple_size", 0]})
      )

    trait =
      Enum.find(
        translated["trait_decls"],
        &(&1 &&
            &1["item_meta"]["lang_item"] == "Copy")
      )

    impl =
      Enum.find(
        translated["trait_impls"],
        &(&1 &&
            &1["impl_trait"]["id"] == trait["def_id"])
      )

    %{document: document, translated: translated, function: function, trait: trait, impl: impl}
  end

  test "checks actual Copy evidence without claiming native deallocation correctness", ctx do
    assert {:ok, %{erasures: entries}} = audit(ctx.translated, ctx.function)
    trait = ctx.trait["def_id"]
    impl = ctx.impl["def_id"]

    assert [
             %{
               type: "alloc::vec::Vec<rustler::term::Term>",
               element_drop_basis: %{
                 kind: :compiler_copy,
                 trait_id: ^trait,
                 implementation_id: ^impl
               },
               implementation_verified: false,
               first_party: false,
               status: :modelled
             }
           ] =
             Map.values(entries)
  end

  test "rejects missing, conditional, negative or mismatched Copy implementations", ctx do
    for replacement <- [
          nil,
          Map.put(ctx.impl, "is_negative", true),
          Map.put(ctx.impl, "is_unsafe", true),
          put_in(ctx.impl, ["item_meta", "has_errors"], true),
          put_in(ctx.impl, ["generics", "trait_clauses"], [%{}]),
          put_in(ctx.impl, ["generics", "types"], [%{"index" => 0}]),
          put_in(ctx.impl, ["impl_trait", "generics", "types"], [%{"Scalar" => "Bool"}]),
          Map.put(ctx.impl, "methods", [%{}])
        ] do
      translated = replace(ctx.translated, "trait_impls", ctx.impl, replacement)
      assert {:error, _, message} = audit(translated, ctx.function)
      assert message =~ "Vec drop"
    end
  end

  test "requires the compiler builtin Copy trait rather than an arbitrary marker", ctx do
    for replacement <- [
          put_in(ctx.trait, ["item_meta", "lang_item"], nil),
          put_in(ctx.trait, ["item_meta", "name"], [%{"Ident" => ["Copy", 0]}]),
          Map.put(ctx.trait, "is_unsafe", true),
          Map.put(ctx.trait, "methods", [%{}])
        ] do
      translated = replace(ctx.translated, "trait_decls", ctx.trait, replacement)
      assert {:error, _, _} = audit(translated, ctx.function)
    end
  end

  test "rejects duplicate Copy evidence even when identities are repeated", ctx do
    for {section, item} <- [{"trait_decls", ctx.trait}, {"trait_impls", ctx.impl}] do
      translated = Map.update!(ctx.translated, section, &(&1 ++ [item]))

      assert_raise ArgumentError, ~r/duplicate declaration identity/, fn ->
        audit(translated, ctx.function)
      end
    end
  end

  test "rejects ambiguous distinct Copy implementations for the same element", ctx do
    extra = Map.put(ctx.impl, "def_id", 999_999)
    translated = Map.update!(ctx.translated, "trait_impls", &(&1 ++ [extra]))
    assert {:error, _, _} = audit(translated, ctx.function)
  end

  defp audit(translated, function) do
    refs = LLBC.type_references!(%{"translated" => translated})
    DropModels.audit([function], [], translated, refs, ["experiment_nif"])
  end

  defp replace(translated, section, old, replacement) do
    Map.update!(
      translated,
      section,
      &Enum.map(&1, fn
        ^old -> replacement
        other -> other
      end)
    )
  end
end
