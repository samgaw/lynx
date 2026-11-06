defmodule Lynx.Rust.EndianModelsTest do
  use ExUnit.Case, async: true
  alias Lynx.Rust.CallModels

  defp function(signed, bits, method) do
    name = if(signed == "Signed", do: "I", else: "U") <> Integer.to_string(bits)
    scalar = %{"Scalar" => %{"Integer" => %{signed => name}}}
    usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}

    array = %{
      "Array" => [
        %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}},
        [%{"Integer" => %{"Unsigned" => ["Usize", Integer.to_string(div(bits, 8))]}}, usize],
        nil
      ]
    }

    params =
      Map.new(
        ~w(regions types const_generics trait_clauses outlives trait_type_constraints),
        &{&1, []}
      )

    {input, output} =
      if String.starts_with?(method, "to_"), do: {scalar, array}, else: {array, scalar}

    %{
      "def_id" => 1,
      "body" => "Opaque",
      "src" => "Normal",
      "generics" => params,
      "item_meta" => %{
        "name" => [
          %{"Ident" => ["core", 0]},
          %{"Ident" => ["num", 0]},
          %{
            "Impl" => %{
              "Ty" => %{
                "kind" => "InherentImplBlock",
                "params" => params,
                "skip_binder" => scalar
              }
            }
          },
          %{"Ident" => [method, 0]}
        ]
      },
      "signature" => %{
        "is_unsafe" => false,
        "is_variadic" => false,
        "abi" => "Rust",
        "inputs" => [input],
        "output" => output
      }
    }
  end

  defp resolve(function), do: CallModels.resolve([function], %{}, %{}, [])

  test "all fixed-width signed and unsigned byte orders reuse the existing Aeneas models" do
    for signed <- ~w(Signed Unsigned),
        bits <- [8, 16, 32, 64, 128],
        method <- ~w(to_le_bytes to_be_bytes from_le_bytes from_be_bytes) do
      f = function(signed, bits, method)
      type = if(signed == "Signed", do: "I", else: "U") <> Integer.to_string(bits)
      expected = "Aeneas.Std.core.num.#{type}.#{method}"

      assert %{
               1 => %{
                 lean: ^expected,
                 builtin: true,
                 can_fail: false,
                 implementation_verified: false,
                 status: :modelled
               }
             } = resolve(f)
    end
  end

  test "rejects mismatched widths, ABI, parent identities, generics and operation names" do
    f = function("Unsigned", 32, "to_be_bytes")
    parent = ["item_meta", "name", Access.at(2), "Impl", "Ty"]

    for bad <- [
          put_in(f, ["body"], %{"Structured" => %{}}),
          put_in(f, ["src"], "GlobalInitializer"),
          put_in(f, ["signature", "abi"], "C"),
          put_in(f, ["signature", "is_unsafe"], true),
          put_in(f, ["signature", "is_variadic"], true),
          put_in(f, ["signature", "inputs"], []),
          put_in(
            f,
            ["signature", "output"],
            function("Unsigned", 16, "to_be_bytes")["signature"]["output"]
          ),
          put_in(f, ["generics", "outlives"], [%{}]),
          put_in(f, parent ++ ["params", "types"], [%{}]),
          put_in(f, parent ++ ["kind"], "TraitImplBlock"),
          put_in(f, parent ++ ["skip_binder"], %{"Scalar" => "Bool"}),
          put_in(f, ["item_meta", "name", Access.at(0)], %{"Ident" => ["lookalike", 0]}),
          put_in(f, ["item_meta", "name", Access.at(3)], %{"Ident" => ["to_ne_bytes", 0]}),
          put_in(f, ["signature", "output"], %{
            "Array" => [
              %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}},
              [
                %{"Integer" => %{"Unsigned" => ["Usize", "4"]}},
                %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}
              ],
              nil
            ]
          })
        ] do
      assert resolve(bad) == %{}
    end
  end
end
