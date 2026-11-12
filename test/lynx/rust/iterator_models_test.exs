defmodule Lynx.Rust.IteratorModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{CallModels, IteratorModels}
  @fixture Path.expand("../../fixtures/rust_iterators/metadata.json", __DIR__)

  # Captured from the standard-library calls in an actual shared-slice for loop.
  # Source spans and docs are omitted; nominal identities and binders are retained.
  defp metadata, do: JSON.decode!(File.read!(@fixture))

  defp function(data, name),
    do:
      Enum.find(
        data["fun_decls"],
        &(List.last(&1["item_meta"]["name"]) == %{"Ident" => [name, 0]})
      )

  test "reuses the upstream shared-slice conversion and next models" do
    data = metadata()
    into = function(data, "into_iter")
    next = function(data, "next")

    assert %{
             30 => %{slice_iterator: "into_iter", builtin: true, implementation_verified: false},
             31 => %{slice_iterator: "next", builtin: true, implementation_verified: false}
           } = CallModels.resolve([into, next], data, %{}, [])
  end

  test "complete method capture does not approve unused iterator methods" do
    data = metadata()

    changed =
      update_in(data, ["trait_impls", Access.at(1), "methods"], fn methods ->
        List.replace_at(methods, 1, %{
          "kind" => %{"TraitMethod" => [10, 1]},
          "skip_binder" => %{"id" => 999}
        })
      end)

    into = function(changed, "into_iter")
    next = function(changed, "next")

    assert %{30 => %{slice_iterator: "into_iter"}, 31 => %{slice_iterator: "next"}} =
             CallModels.resolve([into, next], changed, %{}, [])

    unknown = put_in(next, ["item_meta", "name", Access.at(4)], %{"Ident" => ["nth", 0]})
    assert IteratorModels.resolve(unknown, changed, %{}) == nil
  end

  test "rejects incompatible signatures, ownership, lifetimes and trait selections" do
    data = metadata()
    next = function(data, "next")

    for changed <- [
          put_in(next, ["signature", "is_unsafe"], true),
          put_in(next, ["signature", "abi"], "C"),
          put_in(next, ["signature", "is_variadic"], true),
          put_in(next, ["signature", "inputs", Access.at(0), "Ref", Access.at(2)], "Shared"),
          put_in(
            next,
            [
              "signature",
              "output",
              "Adt",
              "generics",
              "types",
              Access.at(0),
              "Ref",
              Access.at(2)
            ],
            "Mut"
          ),
          put_in(
            next,
            [
              "signature",
              "output",
              "Adt",
              "generics",
              "types",
              Access.at(0),
              "Ref",
              Access.at(0)
            ],
            "Static"
          ),
          put_in(next, ["src", "TraitImpl", "reuses_default"], true),
          put_in(next, ["src", "TraitImpl", "trait_ref", "id"], 999),
          put_in(next, ["src", "TraitImpl", "impl_ref", "generics", "types"], []),
          put_in(next, ["generics", "outlives"], []),
          put_in(next, ["body"], %{"Structured" => %{}})
        ] do
      assert IteratorModels.resolve(changed, data, %{}) == nil
    end
  end

  test "conversion requires its matching iterator implementation and standard Option" do
    data = metadata()
    into = function(data, "into_iter")
    next = function(data, "next")
    assert into["def_id"] == 30

    for changed <- [
          put_in(data, ["fun_decls"], [into]),
          update_in(data, ["trait_impls", Access.at(0), "implied_trait_refs"], fn _ -> [] end),
          put_in(
            data,
            [
              "trait_impls",
              Access.at(0),
              "implied_trait_refs",
              Access.at(0),
              "skip_binder",
              "kind",
              "TraitImpl",
              "id"
            ],
            999
          ),
          put_in(
            data,
            [
              "trait_impls",
              Access.at(1),
              "methods",
              Access.at(0),
              "skip_binder",
              "generics",
              "types"
            ],
            []
          ),
          put_in(data, ["trait_impls", Access.at(1), "is_negative"], true),
          put_in(data, ["type_decls", Access.at(0), "kind", "Enum", Access.at(1), "fields"], []),
          put_in(data, ["type_decls", Access.at(1), "item_meta", "name"], [
            %{"Ident" => ["OtherIterator", 0]}
          ])
        ] do
      assert IteratorModels.resolve(into, changed, %{}) == nil
    end

    wrong_option =
      put_in(data, ["type_decls", Access.at(0), "kind", "Enum", Access.at(1), "discriminant"], %{
        "Signed" => ["Isize", "2"]
      })

    assert IteratorModels.resolve(next, wrong_option, %{}) == nil
  end
end
