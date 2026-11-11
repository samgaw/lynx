defmodule Lynx.Rustler.AtomCopyTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.DropModels
  @snapshot Path.expand("../../fixtures/rustler/atom_copy.json", __DIR__)

  setup do
    %{"translated" => translated} = JSON.decode!(File.read!(@snapshot))
    [atom] = translated["type_decls"]
    [trait] = translated["trait_decls"]
    [impl] = translated["trait_impls"]

    type = %{
      "Adt" => %{
        "id" => atom["def_id"],
        "builtin" => nil,
        "generics" => %{
          "regions" => [],
          "types" => [],
          "const_generics" => [],
          "trait_refs" => []
        }
      }
    }

    %{translated: translated, type: type, trait: trait, impl: impl}
  end

  test "uses the actual unconditional compiler Copy implementation", ctx do
    assert {"rustler::types::atom::Atom",
            %{kind: :compiler_copy, trait_id: trait, implementation_id: impl}} =
             DropModels.nondestructive_payload(ctx.type, ctx.translated, %{})

    assert trait == ctx.trait["def_id"]
    assert impl == ctx.impl["def_id"]

    assert DropModels.metadata_arguments([
             %{rust: "rustler::types::atom::Atom", lean: "Lynx.Rustler.Atom"}
           ]) == [
             "--start-from",
             "{impl core::marker::Copy for rustler::types::atom::Atom}",
             "--include",
             "core::marker::Copy"
           ]
  end

  test "missing or altered Copy evidence never certifies a payload", ctx do
    for translated <- [
          %{ctx.translated | "trait_decls" => []},
          %{ctx.translated | "trait_impls" => []},
          %{ctx.translated | "trait_impls" => [ctx.impl, ctx.impl]},
          %{ctx.translated | "trait_impls" => [Map.put(ctx.impl, "is_negative", true)]},
          %{ctx.translated | "trait_impls" => [Map.put(ctx.impl, "is_unsafe", true)]},
          %{
            ctx.translated
            | "trait_impls" => [put_in(ctx.impl, ["item_meta", "has_errors"], true)]
          },
          %{
            ctx.translated
            | "trait_decls" => [put_in(ctx.trait, ["item_meta", "lang_item"], "Clone")]
          },
          %{ctx.translated | "trait_decls" => [Map.put(ctx.trait, "methods", [%{}])]}
        ] do
      assert DropModels.nondestructive_payload(ctx.type, translated, %{}) == nil
    end

    refute DropModels.nondestructive_payload(
             %{"TypeVar" => %{"Free" => 0}},
             ctx.translated,
             %{}
           )
  end
end
