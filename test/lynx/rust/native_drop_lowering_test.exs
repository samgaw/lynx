defmodule Lynx.Rust.NativeDropLoweringTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.NativeDropLowering

  test "runtime lifetime instantiation preserves nominal identity, payload and borrow permissions" do
    scalar = %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}

    args = %{
      "regions" => [%{"Var" => %{"Free" => 0}}],
      "types" => [scalar],
      "const_generics" => [],
      "trait_refs" => []
    }

    type = %{
      "Ref" => [
        %{"Var" => %{"Free" => 1}},
        %{"Adt" => %{"id" => 4, "builtin" => nil, "generics" => args}},
        "Mut"
      ]
    }

    instantiated = %{
      "Ref" => [
        %{"Body" => 9},
        put_in(Enum.at(type["Ref"], 1), ["Adt", "generics", "regions"], ["Erased"]),
        "Mut"
      ]
    }

    assert NativeDropLowering.same_runtime_type?(type, instantiated)

    for changed <- [
          put_in(instantiated, ["Ref"], [
            %{"Body" => 9},
            Enum.at(instantiated["Ref"], 1),
            "Shared"
          ]),
          %{
            "Ref" => [
              %{"Body" => 9},
              %{"Adt" => %{"id" => 5, "builtin" => nil, "generics" => args}},
              "Mut"
            ]
          },
          %{
            "Ref" => [
              %{"Body" => 9},
              %{
                "Adt" => %{
                  "id" => 4,
                  "builtin" => nil,
                  "generics" => Map.put(args, "regions", [])
                }
              },
              "Mut"
            ]
          },
          %{
            "Ref" => [
              %{"Body" => 9},
              %{
                "Adt" => %{
                  "id" => 4,
                  "builtin" => nil,
                  "generics" =>
                    Map.put(args, "types", [%{"Scalar" => %{"Integer" => %{"Signed" => "I64"}}}])
                }
              },
              "Mut"
            ]
          }
        ],
        do: refute(NativeDropLowering.same_runtime_type?(type, changed))

    refute NativeDropLowering.same_runtime_type?(%{"TypeVar" => %{"Free" => 0}}, %{
             "TypeVar" => %{"Free" => 1}
           })
  end
end
