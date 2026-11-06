defmodule Lynx.Rust.MutexModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{MutexModels, NativeCodecs}

  defp parameters,
    do: %{
      "regions" => [],
      "types" => [%{"index" => 0}],
      "const_generics" => [],
      "trait_clauses" => [],
      "outlives" => [],
      "trait_type_constraints" => []
    }

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp adt(id, types),
    do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => arguments(types)}}

  defp fixture do
    type = %{
      "def_id" => 7,
      "kind" => "Opaque",
      "generics" => parameters(),
      "item_meta" => %{
        "name" => Enum.map(~w(std sync poison mutex Mutex), &%{"Ident" => [&1, 0]})
      }
    }

    function = %{
      "def_id" => 20,
      "body" => "Opaque",
      "src" => "Normal",
      "generics" => parameters(),
      "item_meta" => %{
        "name" =>
          Enum.map(~w(std sync poison mutex), &%{"Ident" => [&1, 0]}) ++
            [
              %{
                "Impl" => %{
                  "Ty" => %{
                    "kind" => "InherentImplBlock",
                    "params" => parameters(),
                    "skip_binder" => adt(7, [%{"TypeVar" => %{"Bound" => [0, 0]}}])
                  }
                }
              },
              %{"Ident" => ["new", 0]}
            ]
      },
      "signature" => %{
        "abi" => "Rust",
        "is_unsafe" => false,
        "is_variadic" => false,
        "inputs" => [%{"TypeVar" => %{"Free" => 0}}],
        "output" => adt(7, [%{"TypeVar" => %{"Free" => 0}}])
      }
    }

    {function, %{"type_decls" => [type]}}
  end

  test "admits only the exact safe standard mutex constructor and nominal type" do
    {function, translated} = fixture()

    assert %{can_fail: true, lift: true, native_mutex_type: 7} =
             MutexModels.resolve(function, translated, %{})

    for invalid <- [
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["signature", "is_variadic"], true),
          put_in(function, ["signature", "output"], adt(8, [%{"TypeVar" => %{"Free" => 0}}])),
          put_in(function, ["generics", "outlives"], ["unapproved"]),
          put_in(function, ["item_meta", "name"], [%{"Ident" => ["shadow", 0]}]),
          put_in(function, ["signature", "inputs"], [])
        ],
        do: assert(is_nil(MutexModels.resolve(invalid, translated, %{})))

    for change <- [
          &put_in(&1, ["kind"], %{"Struct" => []}),
          &put_in(&1, ["item_meta", "name"], [%{"Ident" => ["shadow", 0]}]),
          &put_in(&1, ["generics", "types"], [])
        ] do
      altered = update_in(translated, ["type_decls"], fn [type] -> [change.(type)] end)
      assert is_nil(MutexModels.resolve(function, altered, %{}))
    end
  end

  defp audit(id, field_type) do
    params = Map.put(parameters(), "types", [])

    field = %{
      "name" => "value",
      "is_positional" => false,
      "attr_info" => %{"rename" => nil},
      "ty" => field_type
    }

    type = %{
      "def_id" => id,
      "generics" => params,
      "kind" => %{"Struct" => [field]},
      "item_meta" => %{
        "name" => Enum.map(~w(first_party Counter), &%{"Ident" => [&1, 0]}),
        "attr_info" => %{"rename" => nil}
      }
    }

    %{
      external_calls: %{20 => %{native_mutex_type: 7, native_constructor: true}},
      references: %{},
      first_party: ["first_party"],
      translated: %{"type_decls" => [type]},
      functions: [
        %{
          "body" => %{
            "Regular" => %{"kind" => %{"Fun" => 20}, "generics" => arguments([adt(id, [])])}
          }
        }
      ]
    }
  end

  test "heap type identities survive extraction-local renumbering and reject layout changes" do
    scalar = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}
    [original] = NativeCodecs.plan!(audit(1, scalar))
    [renumbered] = NativeCodecs.plan!(audit(99, scalar))
    [changed] = NativeCodecs.plan!(audit(1, %{"Scalar" => "Bool"}))
    assert original.native_tag == renumbered.native_tag
    refute original.native_tag == changed.native_tag

    assert_raise ArgumentError, ~r/unsupported native heap payload/, fn ->
      NativeCodecs.plan!(audit(1, %{"TypeVar" => %{"Free" => 0}}))
    end
  end
end
