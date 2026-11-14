defmodule Lynx.Rust.AtomicModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.{AtomicModels, ResourceModels}
  @u64 %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}

  defp path(names), do: Enum.map(names, &%{"Ident" => [&1, 0]})

  defp params(types, regions),
    do: %{
      "types" => Enum.map(types, &%{"index" => &1}),
      "regions" => Enum.map(regions, &%{"index" => &1}),
      "const_generics" => [],
      "trait_clauses" => [],
      "trait_type_constraints" => [],
      "outlives" => []
    }

  defp adt(id, types \\ []),
    do: %{
      "Adt" => %{
        "id" => id,
        "builtin" => nil,
        "generics" => ResourceModels.args(types)
      }
    }

  defp fixture(method) do
    atomic = adt(5, [@u64, adt(8, [@u64])])

    types = [
      %{
        "def_id" => 5,
        "kind" => "Opaque",
        "generics" => params([0, 1], []),
        "item_meta" => %{"name" => path(~w(core sync atomic Atomic))}
      },
      %{
        "def_id" => 8,
        "kind" => "Opaque",
        "generics" => params([0], []),
        "item_meta" => %{"name" => path(~w(core sync atomic private Align8))}
      },
      %{
        "def_id" => 6,
        "generics" => params([], []),
        "item_meta" => %{"name" => path(~w(core sync atomic Ordering))},
        "kind" => %{
          "Enum" =>
            Enum.with_index(~w(Relaxed Release Acquire AcqRel SeqCst))
            |> Enum.map(fn {name, id} -> %{"id" => id, "name" => name, "fields" => []} end)
        }
      }
    ]

    borrowed = %{"Ref" => [%{"Var" => %{"Free" => 0}}, atomic, "Shared"]}
    inputs = if method == "load", do: [borrowed, adt(6)], else: [borrowed, @u64, adt(6)]

    output =
      if method == "store",
        do: %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => ResourceModels.args([])}},
        else: @u64

    function = %{
      "def_id" => 22,
      "body" => "Opaque",
      "src" => "Normal",
      "generics" => params([], [0]),
      "signature" => %{
        "inputs" => inputs,
        "output" => output,
        "is_unsafe" => false,
        "is_variadic" => false,
        "abi" => "Rust"
      },
      "item_meta" => %{
        "name" =>
          path(~w(core sync atomic)) ++
            [
              %{
                "Impl" => %{
                  "Ty" => %{
                    "kind" => "InherentImplBlock",
                    "params" => params([], []),
                    "skip_binder" => atomic
                  }
                }
              },
              %{"Ident" => [method, 0]}
            ]
      }
    }

    {function, %{"type_decls" => types, "global_decls" => [], "files" => []}, atomic}
  end

  test "matches actual atomic width, storage, safe signature and ordering layout" do
    for method <- ~w(load store fetch_add) do
      {function, translated, _} = fixture(method)

      assert %{
               native_atomic_type: 5,
               native_atomic_storage_type: 8,
               native_atomic_ordering_type: 6
             } =
               AtomicModels.resolve(function, translated, %{})

      for changed <- [
            put_in(function, ["signature", "is_unsafe"], true),
            put_in(function, ["signature", "is_variadic"], true),
            put_in(function, ["signature", "abi"], "C"),
            put_in(function, ["signature", "inputs"], []),
            put_in(function, ["signature", "output"], "Never"),
            put_in(function, ["generics", "regions"], [%{"index" => 1}]),
            put_in(function, ["generics", "trait_clauses"], [%{}]),
            Map.put(function, "src", "TraitImpl")
          ],
          do: assert(is_nil(AtomicModels.resolve(changed, translated, %{})))

      [atomic, storage, order] = translated["type_decls"]

      for types <- [
            [put_in(atomic, ["item_meta", "name"], path(~w(other Atomic))), storage, order],
            [
              atomic,
              put_in(storage, ["item_meta", "name"], path(~w(core sync atomic private Align4))),
              order
            ],
            [
              atomic,
              storage,
              put_in(order, ["kind", "Enum"], Enum.reverse(order["kind"]["Enum"]))
            ],
            [atomic, storage, Map.put(order, "kind", "Opaque")]
          ],
          do:
            assert(
              is_nil(AtomicModels.resolve(function, %{translated | "type_decls" => types}, %{}))
            )
    end
  end

  test "rejects weaker orderings, dynamic ordering, owned and aggregate cells" do
    {external, translated, atomic} = fixture("fetch_add")
    models = %{22 => AtomicModels.resolve(external, translated, %{})}
    borrowed = hd(external["signature"]["inputs"])

    function = %{
      "item_meta" => %{"name" => path(~w(example claim))},
      "signature" => %{"inputs" => [borrowed], "output" => @u64},
      "generics" => params([], [0]),
      "body" => %{"Aggregate" => [%{"Adt" => [%{"id" => 6}, 4, ResourceModels.args([])]}, []]}
    }

    assert :ok = AtomicModels.audit!([function], models, translated, %{})

    for variant <- 0..3 do
      invalid =
        put_in(function, ["body", "Aggregate"], [
          %{"Adt" => [%{"id" => 6}, variant, ResourceModels.args([])]},
          []
        ])

      assert_raise CompileError, ~r/only Ordering::SeqCst/, fn ->
        AtomicModels.audit!([invalid], models, translated, %{})
      end
    end

    assert_raise CompileError, ~r/ordering parameters/, fn ->
      AtomicModels.audit!(
        [put_in(function, ["signature", "inputs"], [borrowed, adt(6)])],
        models,
        translated,
        %{}
      )
    end

    assert_raise CompileError, ~r/only shared borrows/, fn ->
      AtomicModels.audit!(
        [put_in(function, ["signature", "inputs"], [atomic])],
        models,
        translated,
        %{}
      )
    end

    wrapped = %{"def_id" => 9, "kind" => %{"Struct" => [%{"ty" => atomic}]}}

    assert_raise ArgumentError, ~r/aggregate fields/, fn ->
      AtomicModels.audit!(
        [function],
        models,
        Map.update!(translated, "type_decls", &(&1 ++ [wrapped])),
        %{}
      )
    end
  end
end
