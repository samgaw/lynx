defmodule Lynx.Rust.ArrayModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.ArrayModels

  defp params(regions),
    do: %{
      "regions" => Enum.map(regions, &%{"index" => &1}),
      "types" => [%{"index" => 0}],
      "trait_clauses" => [],
      "trait_type_constraints" => [],
      "outlives" => [],
      "const_generics" => [
        %{"index" => 0, "ty" => %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}}
      ]
    }

  defp fixture(method, mutability) do
    t = %{"TypeVar" => %{"Free" => 0}}

    array = %{
      "Array" => [
        t,
        [%{"Var" => %{"Free" => 0}}, %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}],
        nil
      ]
    }

    parent = %{
      "Array" => [
        %{"TypeVar" => %{"Bound" => [0, 0]}},
        [
          %{"Var" => %{"Bound" => [0, 0]}},
          %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
        ],
        nil
      ]
    }

    ref = fn type -> %{"Ref" => [%{"Var" => %{"Free" => 0}}, type, mutability]} end

    %{
      "body" => "Opaque",
      "src" => "Normal",
      "generics" => params([0]),
      "signature" => %{
        "is_unsafe" => false,
        "is_variadic" => false,
        "abi" => "Rust",
        "inputs" => [ref.(array)],
        "output" => ref.(%{"Slice" => [t, nil]})
      },
      "item_meta" => %{
        "name" => [
          %{"Ident" => ["core", 0]},
          %{"Ident" => ["array", 0]},
          %{
            "Impl" => %{
              "Ty" => %{
                "kind" => "InherentImplBlock",
                "params" => params([]),
                "skip_binder" => parent
              }
            }
          },
          %{"Ident" => [method, 0]}
        ]
      }
    }
  end

  test "array views preserve exact array, const length and borrow mutability" do
    for {method, mutability, lean} <- [
          {"as_slice", "Shared", "to_slice"},
          {"as_mut_slice", "Mut", "to_slice_mut"}
        ] do
      f = fixture(method, mutability)
      expected = "Aeneas.Std.Array." <> lean
      assert %{lean: ^expected, can_fail: false} = ArrayModels.resolve(f, %{}, %{})

      for altered <- [
            put_in(f, ["signature", "is_unsafe"], true),
            put_in(f, ["signature", "is_variadic"], true),
            put_in(f, ["signature", "abi"], "C"),
            put_in(f, ["signature", "inputs"], []),
            put_in(f, ["signature", "output"], %{"Scalar" => "Bool"}),
            put_in(f, ["generics", "const_generics"], []),
            put_in(f, ["generics", "trait_clauses"], [%{}]),
            Map.put(f, "src", "TraitImpl")
          ],
          do: assert(is_nil(ArrayModels.resolve(altered, %{}, %{})))
    end
  end
end
