defmodule Lynx.Rust.OptionModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.CallModels

  test "successful Option expect requires the actual standard layout and consuming signature" do
    params = fn regions ->
      %{
        "regions" => regions,
        "types" => [%{"index" => 0}],
        "const_generics" => [],
        "trait_clauses" => [],
        "outlives" => [],
        "trait_type_constraints" => []
      }
    end

    args = fn types ->
      %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}
    end

    variable = %{"TypeVar" => %{"Free" => 0}}
    input = %{"Adt" => %{"id" => 3, "builtin" => nil, "generics" => args.([variable])}}

    option = %{
      "def_id" => 3,
      "generics" => params.([]),
      "item_meta" => %{"name" => Enum.map(~w(core option Option), &%{"Ident" => [&1, 0]})},
      "kind" => %{
        "Enum" => [
          %{
            "id" => 0,
            "name" => "None",
            "fields" => [],
            "discriminant" => %{"Signed" => ["Isize", "0"]}
          },
          %{
            "id" => 1,
            "name" => "Some",
            "fields" => [%{"ty" => variable}],
            "discriminant" => %{"Signed" => ["Isize", "1"]}
          }
        ]
      }
    }

    function = %{
      "def_id" => 7,
      "body" => "Opaque",
      "src" => "Normal",
      "generics" => params.([%{"index" => 0}]),
      "item_meta" => %{
        "name" => [
          %{"Ident" => ["core", 0]},
          %{"Ident" => ["option", 0]},
          %{
            "Impl" => %{
              "Ty" => %{
                "kind" => "InherentImplBlock",
                "params" => params.([]),
                "skip_binder" =>
                  put_in(input, ["Adt", "generics", "types"], [
                    %{"TypeVar" => %{"Bound" => [0, 0]}}
                  ])
              }
            }
          },
          %{"Ident" => ["expect", 0]}
        ]
      },
      "signature" => %{
        "abi" => "Rust",
        "is_unsafe" => false,
        "is_variadic" => false,
        "inputs" => [
          input,
          %{
            "Ref" => [
              %{"Var" => %{"Free" => 0}},
              %{"Adt" => %{"id" => 4, "builtin" => "Str", "generics" => args.([])}},
              "Shared"
            ]
          }
        ],
        "output" => variable
      }
    }

    translated = %{"type_decls" => [option]}

    assert %{
             7 => %{
               lean: "Lynx.NativeM.expectSome",
               native_transfer: true,
               native_cutoff_only: true,
               implementation_verified: false
             }
           } =
             CallModels.resolve([function], translated, %{}, [], :runtime)

    assert %{} = CallModels.resolve([function], translated, %{}, [])

    for bad <- [
          put_in(function, ["signature", "is_unsafe"], true),
          put_in(function, ["signature", "abi"], "C"),
          put_in(function, ["signature", "output"], %{"TypeVar" => %{"Free" => 1}}),
          put_in(function, ["generics", "trait_clauses"], [%{}]),
          put_in(function, ["generics", "regions"], []),
          put_in(function, ["body"], %{"Structured" => %{}})
        ] do
      assert %{} = CallModels.resolve([bad], translated, %{}, [], :runtime)
    end

    for bad <- [
          put_in(option, ["item_meta", "name"], [%{"Ident" => ["Option", 0]}]),
          put_in(option, ["generics", "types"], [%{"index" => 1}]),
          put_in(option, ["kind", "Enum", Access.at(1), "discriminant"], %{
            "Signed" => ["Isize", "0"]
          }),
          put_in(option, ["kind", "Enum", Access.at(1), "fields"], [])
        ] do
      assert %{} = CallModels.resolve([function], %{"type_decls" => [bad]}, %{}, [], :runtime)
    end
  end
end
