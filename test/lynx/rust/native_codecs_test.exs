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
