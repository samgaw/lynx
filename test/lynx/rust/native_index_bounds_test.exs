defmodule Lynx.Rust.NativeIndexBoundsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.NativeIndexBounds
  @model %{lean: "Aeneas.Std.core.array.Array.index", builtin: true}
  defp unsigned(width), do: %{"Scalar" => %{"Integer" => %{"Unsigned" => width}}}

  defp args(types, traits \\ []),
    do: %{"types" => types, "regions" => [], "const_generics" => [], "trait_refs" => traits}

  defp literal(value),
    do: [%{"Integer" => %{"Unsigned" => ["Usize", to_string(value)]}}, unsigned("Usize")]

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  defp fixture do
    element = unsigned("U8")
    variable = %{"TypeVar" => %{"Free" => 0}}

    inner = %{
      "regions" => [],
      "outlives" => [],
      "skip_binder" => %{
        "kind" => %{"TraitImpl" => %{"id" => 12, "generics" => args([element])}},
        "trait_decl_ref" => %{
          "id" => 2,
          "generics" => args([unsigned("Usize"), %{"Slice" => [element, nil]}, element])
        }
      }
    }

    outer = %{
      "regions" => [],
      "outlives" => [],
      "skip_binder" => %{
        "kind" => %{
          "TraitImpl" => %{
            "id" => 11,
            "generics" => args([element, unsigned("Usize"), element], [inner])
          }
        },
        "trait_decl_ref" => %{
          "id" => 1,
          "generics" => args([%{"Slice" => [element, nil]}, unsigned("Usize"), element])
        }
      }
    }

    call = %{
      "func" => %{
        "Regular" => %{
          "generics" => %{
            "types" => [element, unsigned("Usize"), element],
            "const_generics" => [literal(2)],
            "regions" => ["Erased"],
            "trait_refs" => [outer]
          }
        }
      },
      "args" => [
        %{
          "Move" => %{
            "ty" => %{"Ref" => ["Erased", %{"Array" => [element, literal(2), nil]}, "Shared"]}
          }
        },
        %{"Const" => literal(1)}
      ]
    }

    params = %{
      "types" => [%{"index" => 0}],
      "regions" => [],
      "const_generics" => [],
      "trait_clauses" => [],
      "trait_type_constraints" => [],
      "outlives" => []
    }

    impls = [
      %{
        "def_id" => 11,
        "src" => "Normal",
        "is_negative" => false,
        "is_unsafe" => false,
        "item_meta" => %{"name" => path(~w(core slice index)) ++ [%{"Impl" => %{"Trait" => 11}}]},
        "impl_trait" => %{
          "id" => 1,
          "generics" =>
            args([
              %{"Slice" => [variable, nil]},
              %{"TypeVar" => %{"Free" => 1}},
              %{"TypeVar" => %{"Free" => 2}}
            ])
        }
      },
      %{
        "def_id" => 12,
        "src" => "Normal",
        "is_negative" => false,
        "is_unsafe" => true,
        "generics" => params,
        "item_meta" => %{"name" => path(~w(core slice index)) ++ [%{"Impl" => %{"Trait" => 12}}]},
        "impl_trait" => %{
          "id" => 2,
          "generics" => args([unsigned("Usize"), %{"Slice" => [variable, nil]}, variable])
        }
      }
    ]

    traits =
      for {id, name} <- [{1, ~w(core ops index Index)}, {2, ~w(core slice index SliceIndex)}],
          do: %{"def_id" => id, "item_meta" => %{"name" => path(name)}}

    {call, %{translated: %{"trait_impls" => impls, "trait_decls" => traits}, references: %{}}}
  end

  test "certifies literal bounds only with the actual standard usize delegation" do
    {call, context} = fixture()
    assert NativeIndexBounds.safe?(call, @model, context)

    for altered <- [
          put_in(call, ["args", Access.at(1)], %{"Const" => literal(2)}),
          put_in(call, ["args", Access.at(1)], %{"Const" => literal(-1)}),
          put_in(call, ["args", Access.at(1)], %{"Copy" => %{"kind" => %{"Local" => 2}}}),
          put_in(call, ["func", "Regular", "generics", "const_generics"], [literal(1)]),
          put_in(call, ["func", "Regular", "generics", "types", Access.at(1)], unsigned("U64")),
          put_in(call, ["func", "Regular", "generics", "trait_refs"], []),
          put_in(call, ["func", "Regular", "generics", "const_generics"], [literal(4_294_967_296)])
        ],
        do: refute(NativeIndexBounds.safe?(altered, @model, context))

    for altered <- [
          put_in(context, [:translated, "trait_impls", Access.at(1), "is_unsafe"], false),
          put_in(context, [:translated, "trait_impls", Access.at(1), "impl_trait", "id"], 99),
          put_in(
            context,
            [:translated, "trait_impls", Access.at(1), "generics", "trait_clauses"],
            [%{}]
          ),
          put_in(
            context,
            [:translated, "trait_decls", Access.at(1), "item_meta", "name"],
            path(~w(custom SliceIndex))
          )
        ],
        do: refute(NativeIndexBounds.safe?(call, @model, altered))

    refute NativeIndexBounds.safe?(call, %{lean: "user.index", builtin: true}, context)
    refute NativeIndexBounds.safe?(call, @model, nil)
  end

  test "borrow safety resolves constants independently of overlapping type references" do
    for offset <- [1, 2] do
      {call, context} = fixture()
      call = put_in(call, ["func", "Regular", "kind"], %{"Fun" => 99})

      first =
        put_in(call, ["args", Access.at(1)], %{"Const" => %{"Value" => [1, literal(offset)]}})

      second = put_in(call, ["args", Access.at(1)], %{"Const" => %{"Deduplicated" => 1}})

      function = %{
        "def_id" => 100,
        "body" => %{
          "Structured" => %{
            "body" => %{
              "statements" => [
                %{"kind" => %{"Call" => %{"call" => first}}},
                %{"kind" => %{"Call" => %{"call" => second}}},
                %{"kind" => "Return"}
              ]
            }
          }
        }
      }

      context = %{
        context
        | translated: Map.put(context.translated, "fun_decls", [function]),
          references: %{1 => unsigned("U8")}
      }

      safe =
        Lynx.Rust.NativeBorrows.nonpanicking_calls(
          [function],
          %{99 => Map.put(@model, :can_fail, true)},
          context
        )

      assert MapSet.member?(safe, 100) == (offset == 1)
    end
  end
end
