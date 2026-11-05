defmodule Lynx.Rust.CallModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.CallModels

  defp slice_length do
    slice = %{"Slice" => [%{"TypeVar" => %{"Free" => 0}}, nil]}

    %{
      "def_id" => 7,
      "body" => "Opaque",
      "item_meta" => %{
        "name" => [
          %{"Ident" => ["core", 0]},
          %{"Ident" => ["slice", 0]},
          %{"Impl" => %{"Ty" => %{"skip_binder" => slice}}},
          %{"Ident" => ["len", 0]}
        ]
      },
      "signature" => %{
        "is_unsafe" => false,
        "is_variadic" => false,
        "abi" => "Rust",
        "inputs" => [%{"Ref" => [%{"Var" => %{"Free" => 0}}, slice, "Shared"]}],
        "output" => %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
      },
      "generics" => %{
        "regions" => [%{"index" => 0}],
        "types" => [%{"index" => 0}],
        "const_generics" => [],
        "trait_clauses" => [],
        "trait_type_constraints" => []
      }
    }
  end

  defp resolve(function), do: CallModels.resolve([function], %{"type_decls" => []}, %{}, [])

  test "approved slice length is explicitly modelled rather than implementation verified" do
    assert %{
             7 => %{
               status: :modelled,
               implementation_verified: false,
               builtin: true,
               lean: "Aeneas.Std.Slice.len"
             }
           } = resolve(slice_length())
  end

  test "model identity includes nominal path, signature, body opacity and generic indices" do
    original = slice_length()
    slice = %{"Slice" => [%{"TypeVar" => %{"Free" => 0}}, nil]}

    for rejected <- [
          put_in(original, ["body"], %{"Structured" => %{}}),
          put_in(original, ["signature", "is_unsafe"], true),
          put_in(original, ["signature", "abi"], "C"),
          put_in(original, ["signature", "is_variadic"], true),
          put_in(original, ["signature", "inputs"], [
            %{"Ref" => [%{"Var" => %{"Free" => 0}}, slice, "Mut"]}
          ]),
          put_in(original, ["signature", "output"], %{
            "Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}
          }),
          put_in(original, ["generics", "regions"], nil),
          put_in(original, ["generics", "types"], [%{"index" => 1}]),
          put_in(original, ["generics", "trait_clauses"], [%{}]),
          put_in(original, ["item_meta", "name"], [%{"Ident" => ["lookalike", 0]}])
        ] do
      assert resolve(rejected) == %{}, inspect(rejected)
    end
  end

  test "u64 saturation reuses the typed primitive model and rejects type or parent mismatches" do
    scalar = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}
    original = slice_length()

    function =
      original
      |> put_in(["item_meta", "name"], [
        %{"Ident" => ["core", 0]},
        %{"Ident" => ["num", 0]},
        %{"Impl" => %{"Ty" => %{"skip_binder" => scalar}}},
        %{"Ident" => ["saturating_add", 0]}
      ])
      |> put_in(["signature", "inputs"], [scalar, scalar])
      |> put_in(["signature", "output"], scalar)
      |> put_in(["generics", "regions"], [])
      |> put_in(["generics", "types"], [])

    assert %{
             7 => %{
               implementation_verified: false,
               status: :modelled,
               rust_name: "core::num::{u64}::saturating_add"
             }
           } = resolve(function)

    for rejected <- [
          put_in(function, ["signature", "inputs"], [scalar]),
          put_in(function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(function, ["generics", "types"], [%{"index" => 0}]),
          put_in(function, ["item_meta", "name", Access.at(2), "Impl", "Ty", "skip_binder"], %{
            "Scalar" => "Bool"
          })
        ] do
      assert resolve(rejected) == %{}
    end
  end

  test "unknown model switches fail closed" do
    assert_raise ArgumentError, ~r/unknown external Rust call model/, fn ->
      CallModels.resolve([], %{}, %{}, [:unknown])
    end
  end
end
