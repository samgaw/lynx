defmodule Lynx.Rust.CollectionModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.CallModels

  defp params(count, regions, outlives) do
    %{
      "types" => Enum.map(0..(count - 1), &%{"index" => &1}),
      "regions" => regions,
      "outlives" => outlives,
      "const_generics" => [],
      "trait_clauses" => [],
      "trait_type_constraints" => []
    }
  end

  defp example(method) do
    t = %{"TypeVar" => %{"Free" => 0}}
    args = %{"types" => [t], "regions" => [], "const_generics" => [], "trait_refs" => []}
    vector = %{"Adt" => %{"id" => 5, "builtin" => nil, "generics" => args}}
    parent = put_in(vector, ["Adt", "generics", "types"], [%{"TypeVar" => %{"Bound" => [0, 0]}}])

    outlives =
      Enum.map(0..1, fn i ->
        %{
          "regions" => [],
          "outlives" => [],
          "skip_binder" => [
            %{"Lub" => %{"TypeVar" => %{"Free" => i}}},
            %{"Var" => %{"Free" => 0}}
          ]
        }
      end)

    kind = if method == "as_slice", do: "Shared", else: "Mut"
    ref = fn type -> %{"Ref" => [%{"Var" => %{"Free" => 0}}, type, kind]} end

    f = %{
      "def_id" => 1,
      "body" => "Opaque",
      "src" => "Normal",
      "generics" => params(2, [%{"index" => 0}], outlives),
      "item_meta" => %{
        "name" => [
          %{"Ident" => ["alloc", 0]},
          %{"Ident" => ["vec", 0]},
          %{
            "Impl" => %{
              "Ty" => %{
                "kind" => "InherentImplBlock",
                "params" => params(2, [], []),
                "skip_binder" => parent
              }
            }
          },
          %{"Ident" => [method, 0]}
        ]
      },
      "signature" => %{
        "is_unsafe" => false,
        "abi" => "Rust",
        "is_variadic" => false,
        "inputs" => [ref.(vector)],
        "output" => ref.(%{"Slice" => [t, nil]})
      }
    }

    types = %{
      "type_decls" => [
        %{
          "def_id" => 5,
          "generics" => params(1, [], []),
          "item_meta" => %{"name" => Enum.map(~w(alloc vec Vec), &%{"Ident" => [&1, 0]})}
        }
      ]
    }

    {f, types}
  end

  test "Vec views reuse Aeneas borrowing and retain explicit generic filtering" do
    for method <- ~w(as_slice as_mut_slice) do
      {f, types} = example(method)
      mut = method == "as_mut_slice"

      assert %{
               1 => %{
                 builtin: false,
                 can_fail: false,
                 lift: ^mut,
                 keep_params: [true, false],
                 implementation_verified: false
               }
             } =
               CallModels.resolve([f], types, %{}, [])
    end
  end

  test "rejects altered view mutability, nominal type, lifetimes and unsafe signatures" do
    {f, types} = example("as_mut_slice")

    for bad <- [
          put_in(f, ["signature", "is_unsafe"], true),
          put_in(f, ["signature", "abi"], "C"),
          put_in(f, ["signature", "output", "Ref", Access.at(2)], "Shared"),
          put_in(f, ["signature", "inputs"], []),
          put_in(f, ["generics", "outlives"], []),
          put_in(f, ["item_meta", "name", Access.at(3)], %{"Ident" => ["into_iter", 0]})
        ] do
      assert CallModels.resolve([bad], types, %{}, []) == %{}
    end

    wrong =
      put_in(types, ["type_decls", Access.at(0), "item_meta", "name"], [
        %{"Ident" => ["FakeVec", 0]}
      ])

    assert CallModels.resolve([f], wrong, %{}, []) == %{}
  end
end
