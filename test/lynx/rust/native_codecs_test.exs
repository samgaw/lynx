defmodule Lynx.Rust.NativeCodecsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{NativeCodecs, NativeDrops, ResourceModels}

  test "signed widths remain distinct lossless native schemas with destructor-free scalars" do
    for width <- ~w(I8 I16 I32 I64 I128 Isize) do
      scalar = %{"Scalar" => %{"Integer" => %{"Signed" => width}}}
      audit = audit(scalar)
      assert [%{native_tag: tag, native_cleanup: :trivial}] = NativeCodecs.plan!(audit)
      assert JSON.decode!(tag) == ["fixture::Balance", [["value", String.downcase(width)]]]
      assert NativeDrops.destructor_free?(scalar, audit.translated, audit.references)
    end

    signed = %{"Scalar" => %{"Integer" => %{"Signed" => "I64"}}}
    unsigned = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}
    assert [%{native_tag: signed_tag}] = NativeCodecs.plan!(audit(signed))
    assert [%{native_tag: unsigned_tag}] = NativeCodecs.plan!(audit(unsigned))
    refute signed_tag == unsigned_tag
  end

  test "unsupported scalar widths and float heap contents are rejected" do
    for scalar <- [
          %{"Scalar" => %{"Integer" => %{"Signed" => "I7"}}},
          %{"Scalar" => %{"Float" => "F64"}}
        ] do
      audit = audit(scalar)
      refute NativeDrops.destructor_free?(scalar, audit.translated, audit.references)

      assert_raise ArgumentError, ~r/unsupported native heap payload/, fn ->
        NativeCodecs.plan!(audit)
      end
    end
  end

  test "scalar enum schemas preserve unit, named and positional variant identities" do
    audit = enum_audit()
    assert [%{native_tag: tag, native_cleanup: :trivial}] = NativeCodecs.plan!(audit)

    assert JSON.decode!(tag) == [
             "fixture::Balance",
             [
               "enum",
               [
                 ["Idle", %{"Signed" => ["Isize", "0"]}, []],
                 ["Named", %{"Signed" => ["Isize", "1"]}, [["value", false, "i64"]]],
                 ["Tuple", %{"Signed" => ["Isize", "2"]}, [["_0", true, "i64"]]]
               ]
             ]
           ]

    type = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => ResourceModels.args([])}}
    assert NativeDrops.destructor_free?(type, audit.translated, audit.references)
  end

  test "enum cleanup requires compiler evidence and primitive fields" do
    for needs_drop <- [nil, true] do
      changed =
        put_in(enum_audit(), [:translated, "type_decls", Access.at(0), "needs_drop"], needs_drop)

      assert_raise ArgumentError, ~r/unsupported scalar enum/, fn ->
        NativeCodecs.plan!(changed)
      end

      type = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => ResourceModels.args([])}}
      refute NativeDrops.destructor_free?(type, changed.translated, changed.references)
    end

    for field <- [
          %{"Ref" => []},
          %{"Scalar" => %{"Float" => "F64"}},
          %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => ResourceModels.args([])}}
        ] do
      changed =
        update_in(
          enum_audit(),
          [
            :translated,
            "type_decls",
            Access.at(0),
            "kind",
            "Enum",
            Access.at(1),
            "fields",
            Access.at(0),
            "ty"
          ],
          fn _ -> field end
        )

      assert_raise ArgumentError, ~r/unsupported scalar enum/, fn ->
        NativeCodecs.plan!(changed)
      end

      type = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => ResourceModels.args([])}}
      refute NativeDrops.destructor_free?(type, changed.translated, changed.references)
    end
  end

  test "enum admission rejects ambiguous variant names, IDs and tuple labels" do
    audit = enum_audit()

    for {path, value} <- [
          {[Access.at(1), "name"], "Idle"},
          {[Access.at(1), "id"], 9},
          {[Access.at(2), "fields", Access.at(0), "name"], "wrong"},
          {[Access.at(1), "attr_info", "rename"], "Other"}
        ] do
      changed =
        put_in(audit, [:translated, "type_decls", Access.at(0), "kind", "Enum"] ++ path, value)

      assert_raise ArgumentError, ~r/unsupported scalar enum/, fn ->
        NativeCodecs.plan!(changed)
      end
    end
  end

  defp enum_audit do
    audit = audit(%{"Scalar" => %{"Integer" => %{"Signed" => "I64"}}})
    [type] = audit.translated["type_decls"]
    [field] = type["kind"]["Struct"]

    variants =
      for {name, fields, index} <- [
            {"Idle", [], 0},
            {"Named", [field], 1},
            {"Tuple", [%{field | "name" => "_0", "is_positional" => true}], 2}
          ] do
        %{
          "id" => index,
          "name" => name,
          "fields" => fields,
          "attr_info" => %{"rename" => nil},
          "discriminant" => %{"Signed" => ["Isize", "#{index}"]}
        }
      end

    put_in(audit, [:translated, "type_decls"], [%{type | "kind" => %{"Enum" => variants}}])
  end

  defp audit(scalar) do
    args = ResourceModels.args([])
    type = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => args}}

    declaration = %{
      "def_id" => 1,
      "needs_drop" => false,
      "generics" => %{
        "regions" => [],
        "types" => [],
        "const_generics" => [],
        "trait_clauses" => [],
        "trait_type_constraints" => [],
        "outlives" => []
      },
      "item_meta" => %{
        "name" => [%{"Ident" => ["fixture", 0]}, %{"Ident" => ["Balance", 0]}],
        "attr_info" => %{"rename" => nil}
      },
      "kind" => %{
        "Struct" => [
          %{
            "name" => "value",
            "is_positional" => false,
            "ty" => scalar,
            "attr_info" => %{"rename" => nil}
          }
        ]
      }
    }

    %{
      external_calls: %{2 => %{native_constructor: true}},
      functions: [
        %{
          "body" => %{
            "Regular" => %{
              "kind" => %{"Fun" => 2},
              "generics" => ResourceModels.args([type])
            }
          }
        }
      ],
      references: %{},
      first_party: ["fixture"],
      translated: %{"type_decls" => [declaration], "options" => %{"owned_drops" => true}}
    }
  end
end
