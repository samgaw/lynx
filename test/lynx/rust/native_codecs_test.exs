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

      assert_raise ArgumentError, ~r/unsupported plain-data enum/, fn ->
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

      assert_raise ArgumentError, ~r/unsupported plain-data enum/, fn ->
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

      assert_raise ArgumentError, ~r/unsupported plain-data enum/, fn ->
        NativeCodecs.plan!(changed)
      end
    end
  end

  test "nested enum data is ordered before users and rejects hidden ownership" do
    audit = enum_audit()
    [outer] = audit.translated["type_decls"]
    [record] = audit(%{"Scalar" => "Bool"}).translated["type_decls"]

    record = %{
      record
      | "def_id" => 3,
        "item_meta" =>
          put_in(record["item_meta"], ["name", Access.at(1)], %{"Ident" => ["Record", 0]})
    }

    inner = %{
      outer
      | "def_id" => 2,
        "item_meta" =>
          put_in(outer["item_meta"], ["name", Access.at(1)], %{"Ident" => ["Inner", 0]})
    }

    adt = fn id ->
      %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => ResourceModels.args([])}}
    end

    field = ["kind", "Enum", Access.at(1), "fields", Access.at(0), "ty"]
    inner = put_in(inner, field, adt.(3))
    outer = put_in(outer, field, adt.(2))
    audit = put_in(audit, [:translated, "type_decls"], [outer, inner, record])

    assert [%{"def_id" => 3}, %{"def_id" => 2}, %{"def_id" => 1, native_tag: tag}] =
             NativeCodecs.plan!(audit)

    assert String.contains?(tag, "fixture::Record")
    assert NativeDrops.plain_data?(adt.(1), audit.translated, %{})

    changed_width =
      put_in(
        audit,
        [:translated, "type_decls", Access.at(2), "kind", "Struct", Access.at(0), "ty"],
        %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}
      )

    assert [_, _, %{native_tag: changed_tag}] = NativeCodecs.plan!(changed_width)
    refute changed_tag == tag

    foreign =
      put_in(
        audit,
        [:translated, "type_decls", Access.at(2), "item_meta", "name", Access.at(0)],
        %{"Ident" => ["external", 0]}
      )

    assert_raise ArgumentError, ~r/unsupported native heap struct identity/, fn ->
      NativeCodecs.plan!(foreign)
    end

    for replacement <- [
          Map.put(record, "needs_drop", true),
          Map.delete(record, "needs_drop"),
          put_in(record, ["kind", "Struct", Access.at(0), "ty"], adt.(1)),
          put_in(record, ["kind", "Struct", Access.at(0), "ty"], %{"Ref" => []}),
          put_in(record, ["kind", "Struct", Access.at(0), "ty"], %{
            "Adt" => %{
              "id" => 4,
              "builtin" => nil,
              "generics" => ResourceModels.args([%{"Scalar" => "Bool"}])
            }
          }),
          Map.put(record, "kind", "Opaque"),
          put_in(record, ["generics", "types"], [%{"index" => 0}])
        ] do
      changed = put_in(audit, [:translated, "type_decls", Access.at(2)], replacement)
      refute NativeDrops.plain_data?(adt.(1), changed.translated, %{})
      refute NativeDrops.destructor_free?(adt.(1), changed.translated, %{})

      assert_raise ArgumentError, ~r/unsupported plain-data enum/, fn ->
        NativeCodecs.plan!(changed)
      end
    end
  end

  test "fixed arrays preserve rank, length and element identity without truncation" do
    byte = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}
    signed = %{"Scalar" => %{"Integer" => %{"Signed" => "I8"}}}

    array = fn element, length ->
      %{
        "Array" => [
          element,
          [
            %{"Integer" => %{"Unsigned" => ["Usize", length]}},
            %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
          ],
          nil
        ]
      }
    end

    for length <- ["0", "8", "262144"] do
      type = array.(byte, length)
      audit = audit(type)
      assert [%{native_tag: tag}] = NativeCodecs.plan!(audit)

      assert JSON.decode!(tag) == [
               "fixture::Balance",
               [["value", ["array", String.to_integer(length), "u8"]]]
             ]

      assert NativeDrops.destructor_free?(type, audit.translated, %{})
    end

    nested = array.(array.(signed, "4"), "2")
    assert [%{native_tag: tag}] = NativeCodecs.plan!(audit(nested))

    assert JSON.decode!(tag) == [
             "fixture::Balance",
             [["value", ["array", 2, ["array", 4, "i8"]]]]
           ]

    for type <- [
          array.(byte, "262145"),
          array.(byte, "-1"),
          array.(byte, "08"),
          array.(byte, "8x"),
          array.(byte, "+8"),
          %{"Array" => [byte, [%{"Var" => %{"Free" => 0}}, %{"Scalar" => "Bool"}], nil]},
          array.(%{"Ref" => []}, "8"),
          array.(%{"Scalar" => %{"Float" => "F64"}}, "8"),
          %{
            "Array" => [
              byte,
              [%{"Integer" => %{"Unsigned" => ["U32", "8"]}}, %{"Scalar" => "Bool"}],
              nil
            ]
          }
        ] do
      audit = audit(type)
      refute NativeDrops.destructor_free?(type, audit.translated, %{})

      assert_raise ArgumentError, ~r/unsupported native array/, fn ->
        NativeCodecs.plan!(audit)
      end
    end
  end

  test "allocator-confirmed byte records have a lossless representation without a cleanup dictionary" do
    byte = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}
    vector = %{"Adt" => %{"id" => 2, "builtin" => nil, "generics" => ResourceModels.args([byte])}}
    initial = audit(vector)
    [record] = initial.translated["type_decls"]

    declaration = %{
      "def_id" => 2,
      "kind" => "Opaque",
      "item_meta" => %{"name" => Enum.map(~w(alloc vec Vec), &%{"Ident" => [&1, 0]})},
      "generics" => Map.put(record["generics"], "types", [%{"index" => 0}])
    }

    changed =
      initial
      |> put_in([:translated, "options", "owned_drops"], false)
      |> put_in([:translated, "type_decls"], [Map.put(record, "needs_drop", true), declaration])

    assert_raise ArgumentError, ~r/unsupported native heap handle/, fn ->
      NativeCodecs.plan!(changed)
    end

    admitted = Map.put(changed, :allocator_layout, %{global_vectors: true})
    assert [%{native_cleanup: nil, native_tag: tag}] = NativeCodecs.plan!(admitted)
    assert JSON.decode!(tag) == ["fixture::Balance", [["value", ["alloc::vec::Vec", "u8"]]]]
    type = %{"Adt" => %{"id" => 1, "builtin" => nil, "generics" => ResourceModels.args([])}}
    refute NativeDrops.destructor_free?(type, admitted.translated, %{})
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
