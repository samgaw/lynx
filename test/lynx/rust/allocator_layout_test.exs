defmodule Lynx.Rust.AllocatorLayoutTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.AllocatorLayout

  test "matches actual vector arguments before and after allocator erasure" do
    assert %{global_vectors: true, functions: [_]} =
             AllocatorLayout.audit!(document(true), document(false), ["first_party"])
  end

  test "rejects unknown, custom and missing allocator arguments" do
    for allocator <- [adt(3, []), %{"TypeVar" => %{"Free" => 0}}, scalar()] do
      bad =
        put_in(
          document(true),
          ["translated", "fun_decls", Access.at(0), "signature", "output"],
          adt(1, [scalar(), allocator])
        )

      assert_raise ArgumentError, ~r/compiler-confirmed Global/, fn ->
        AllocatorLayout.audit!(bad, document(false), ["first_party"])
      end
    end

    bad =
      put_in(
        document(true),
        ["translated", "fun_decls", Access.at(0), "signature", "output"],
        adt(1, [scalar()])
      )

    assert_raise ArgumentError, ~r/missing vector allocator/, fn ->
      AllocatorLayout.audit!(bad, document(false), ["first_party"])
    end
  end

  test "rejects altered source types and extraction configurations" do
    for bad <- [
          put_in(document(true), ["translated", "options", "precise_drops"], false),
          put_in(document(true), ["translated", "options", "hide_allocator"], true),
          put_in(document(true), ["has_errors"], true)
        ] do
      assert_raise ArgumentError, ~r/configuration mismatch/, fn ->
        AllocatorLayout.audit!(bad, document(false), ["first_party"])
      end
    end

    bad =
      put_in(
        document(false),
        ["translated", "fun_decls", Access.at(0), "signature", "output"],
        scalar()
      )

    assert_raise ArgumentError, ~r/type correspondence mismatch/, fn ->
      AllocatorLayout.audit!(document(true), bad, ["first_party"])
    end
  end

  test "requires every first-party declaration and rejects ambiguous identities" do
    bad = put_in(document(true), ["translated", "fun_decls"], [])

    assert_raise ArgumentError, ~r/different first-party declarations/, fn ->
      AllocatorLayout.audit!(bad, document(false), ["first_party"])
    end

    bad = update_in(document(true), ["translated", "fun_decls"], &(&1 ++ &1))

    assert_raise ArgumentError, ~r/ambiguous first-party/, fn ->
      AllocatorLayout.audit!(bad, document(false), ["first_party"])
    end
  end

  test "does not interpret span-cache indices as type references" do
    raw =
      put_in(
        document(true),
        ["translated", "fun_decls", Access.at(0), "body", "Structured", "locals"],
        %{
          "locals" => [
            %{
              "index" => 0,
              "ty" => adt(1, [scalar(), adt(2, [])]),
              "span" => %{"Deduplicated" => 99}
            }
          ]
        }
      )

    normal =
      put_in(
        document(false),
        ["translated", "fun_decls", Access.at(0), "body", "Structured", "locals"],
        %{
          "locals" => [
            %{"index" => 0, "ty" => adt(1, [scalar()]), "span" => %{"Deduplicated" => 100}}
          ]
        }
      )

    assert %{global_vectors: true} = AllocatorLayout.audit!(raw, normal, ["first_party"])
  end

  defp document(preserved) do
    output = adt(1, [scalar()] ++ if(preserved, do: [adt(2, [])], else: []))

    %{
      "charon_version" => "0.1.304",
      "has_errors" => false,
      "translated" => %{
        "crate_name" => "first_party",
        "options" => %{"hide_allocator" => !preserved, "precise_drops" => true},
        "fun_decls" => [
          %{
            "def_id" => 0,
            "item_meta" => %{"name" => path(~w(first_party consume))},
            "signature" => %{"output" => output},
            "body" => %{"Structured" => %{"locals" => %{}}}
          }
        ],
        "type_decls" =>
          Enum.map(
            [{1, ~w(alloc vec Vec)}, {2, ~w(alloc alloc Global)}, {3, ~w(other Custom)}],
            fn {id, name} -> %{"def_id" => id, "item_meta" => %{"name" => path(name)}} end
          ),
        "global_decls" => []
      }
    }
  end

  defp scalar, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}

  defp adt(id, types),
    do: %{
      "Adt" => %{"id" => id, "builtin" => nil, "generics" => Lynx.Rust.ResourceModels.args(types)}
    }

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
end
