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

  test "inspects only checked str and slice length metadata without consuming a borrow" do
    usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
    args = %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}
    string = %{"Adt" => %{"id" => 1, "builtin" => "Str", "generics" => args}}
    slice = %{"Slice" => [%{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}, nil]}

    for pointee <- [string, slice] do
      reference = %{"Ref" => ["Erased", pointee, "Shared"]}
      parent = %{"kind" => %{"Local" => 1}, "ty" => reference}
      place = %{"kind" => %{"Projection" => [parent, "PtrMetadata"]}, "ty" => usize}

      ctx = %{
        locals: %{1 => reference},
        refs: %{},
        translated: %{"files" => []},
        function: %{"item_meta" => %{"name" => [%{"Ident" => ["probe", 0]}]}}
      }

      assert NativeDropLowering.place_type!(place, ctx, true) == usize

      assert_raise CompileError, ~r/cannot consume through a borrowed/, fn ->
        NativeDropLowering.place_type!(place, ctx)
      end

      assert_raise CompileError, ~r/inconsistent field type/, fn ->
        NativeDropLowering.place_type!(Map.put(place, "ty", %{"Scalar" => "Bool"}), ctx, true)
      end

      raw = %{"RawPtr" => [pointee, "Const"]}
      parent = Map.put(parent, "ty", raw)
      raw_place = put_in(place, ["kind", "Projection"], [parent, "PtrMetadata"])

      assert_raise CompileError, ~r/unsupported native ownership pointer metadata/, fn ->
        NativeDropLowering.place_type!(raw_place, %{ctx | locals: %{1 => raw}}, true)
      end
    end
  end
end
