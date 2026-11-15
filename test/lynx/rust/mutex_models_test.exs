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

    assert %{
             can_fail: true,
             lift: true,
             native_mutex_type: 7,
             native_constructor: true,
             native_transfer: true,
             native_cutoff_only: true,
             label: label
           } =
             MutexModels.resolve(function, translated, %{})

    assert label =~ "atomic logical identity allocation"
    assert label =~ "physical initialization/allocation unverified"

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

  test "consuming extraction requires the actual owned signature and poison result" do
    %{"function" => function, "translated" => translated} =
      File.read!(Path.expand("../../fixtures/rustler/mutex_into_inner.json", __DIR__))
      |> JSON.decode!()

    assert %{
             native_codec_owned_input: true,
             native_transfer: true,
             native_cutoff_only: true,
             lean: "Lynx.NativeMutex.into_inner",
             native_poison_type: poison
           } =
             MutexModels.resolve(function, translated, %{})

    for altered <- [
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["signature", "is_variadic"], true),
          put_in(function, ["signature", "inputs"], []),
          put_in(function, ["signature", "inputs", Access.at(0)], %{
            "Ref" => ["Erased", hd(function["signature"]["inputs"]), "Shared"]
          }),
          put_in(function, ["signature", "output", "Adt", "generics", "types", Access.at(0)], %{
            "Scalar" => "Bool"
          }),
          put_in(
            function,
            ["signature", "output", "Adt", "generics", "types", Access.at(1), "Adt", "id"],
            999
          ),
          put_in(function, ["generics", "outlives"], ["unknown"]),
          put_in(function, ["item_meta", "name"], [%{"Ident" => ["user_mutex", 0]}])
        ],
        do: refute(MutexModels.resolve(altered, translated, %{}))

    changed =
      update_in(translated, ["type_decls"], fn types ->
        Enum.map(types, fn type ->
          if type["def_id"] == poison,
            do: put_in(type, ["item_meta", "name"], [%{"Ident" => ["UserPoison", 0]}]),
            else: type
        end)
      end)

    refute MutexModels.resolve(function, changed, %{})
  end

  test "owned mutex input discovers payload codecs without a constructor call" do
    input = audit(1, %{"Scalar" => "Bool"})
    input = %{input | external_calls: %{20 => %{native_codec_owned_input: true}}}
    assert [%{"def_id" => 1}] = NativeCodecs.plan!(input)

    malformed =
      update_in(
        input,
        [:functions, Access.at(0), "body", "Regular", "generics", "regions"],
        fn _ -> ["Erased"] end
      )

    assert_raise ArgumentError, ~r/unsupported native mutex/, fn ->
      NativeCodecs.plan!(malformed)
    end
  end
end
