defmodule Lynx.Rust.ResourceLifetimesTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{ResourceLifetimes, ResourceModels}

  test "derives retirement for primitive lock cells without a Rust destructor" do
    {payload, audit} = fixture(%{"Scalar" => "Bool"})
    assert [{"state", "NativeRwLock.dispose"}] = ResourceLifetimes.cleanup_fields!(payload, audit)
    assert ResourceLifetimes.enabled?(audit.translated)
    refute ResourceLifetimes.enabled?(put_in(audit.translated, ["options", "owned_drops"], true))
  end

  test "rejects missing and observable destructor certificates" do
    {payload, audit} = fixture(%{"Scalar" => "Bool"})

    for needs_drop <- [nil, true] do
      changed = Map.put(payload, "needs_drop", needs_drop)
      audit = put_in(audit, [:translated, "type_decls", Access.at(0)], changed)
      refute ResourceLifetimes.enabled?(audit.translated)

      assert_raise ArgumentError, ~r/compiler-certified no-drop/, fn ->
        ResourceLifetimes.cleanup_fields!(changed, audit)
      end
    end
  end

  test "does not retire unsupported lock contents or counterfeit standard types" do
    for contents <- [%{"Ref" => []}, %{"Scalar" => %{"Integer" => %{"Signed" => "I64"}}}] do
      {payload, audit} = fixture(contents)

      assert_raise ArgumentError, ~r/primitive payload/, fn ->
        ResourceLifetimes.cleanup_fields!(payload, audit)
      end
    end

    {payload, audit} = fixture(%{"Scalar" => "Bool"})

    changed =
      put_in(
        audit,
        [:translated, "type_decls", Access.at(1), "item_meta", "name"],
        path(~w(application RwLock))
      )

    refute ResourceLifetimes.enabled?(changed.translated)

    assert_raise ArgumentError, ~r/field ownership/, fn ->
      ResourceLifetimes.cleanup_fields!(payload, changed)
    end
  end

  test "requires the actual Resource trait identity" do
    {_payload, audit} = fixture(%{"Scalar" => "Bool"})

    changed =
      put_in(
        audit.translated,
        ["trait_decls", Access.at(0), "item_meta", "name"],
        path(~w(application Resource))
      )

    refute ResourceLifetimes.enabled?(changed)
  end

  defp fixture(contents) do
    parameters = %{
      "regions" => [],
      "types" => [],
      "const_generics" => [],
      "trait_clauses" => [],
      "trait_type_constraints" => [],
      "outlives" => []
    }

    payload = %{
      "def_id" => 0,
      "needs_drop" => false,
      "generics" => parameters,
      "kind" => %{"Struct" => [%{"name" => "state", "ty" => adt(1, [contents])}]}
    }

    lock = %{
      "def_id" => 1,
      "kind" => "Opaque",
      "item_meta" => %{"name" => path(~w(std sync poison rwlock RwLock))},
      "generics" => %{parameters | "types" => [%{"index" => 0}]}
    }

    translated = %{
      "options" => %{},
      "type_decls" => [payload, lock],
      "trait_decls" => [
        %{
          "def_id" => 2,
          "item_meta" => %{
            "name" => path(~w(rustler resource traits Resource))
          }
        }
      ],
      "trait_impls" => [
        %{"impl_trait" => %{"id" => 2, "generics" => ResourceModels.args([adt(0, [])])}}
      ]
    }

    {payload, %{translated: translated, references: %{}}}
  end

  defp adt(id, types),
    do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => ResourceModels.args(types)}}

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
end
