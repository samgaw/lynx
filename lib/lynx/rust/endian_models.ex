defmodule Lynx.Rust.EndianModels do
  @moduledoc false
  alias Lynx.Rust.CallModels

  @widths (for signed <- ["Signed", "Unsigned"], bits <- [8, 16, 32, 64, 128], into: %{} do
             prefix = if signed == "Signed", do: "I", else: "U"
             {{signed, prefix <> Integer.to_string(bits)}, div(bits, 8)}
           end)

  def resolve(function, _translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "generics" => params,
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["core", 0]},
               %{"Ident" => ["num", 0]},
               %{
                 "Impl" => %{
                   "Ty" => %{
                     "kind" => "InherentImplBlock",
                     "params" => parent_params,
                     "skip_binder" => parent
                   }
                 }
               },
               %{"Ident" => [method, 0]}
             ]
           }
         } <- function,
         true <- empty_parameters?(params) and empty_parameters?(parent_params),
         true <- method in ~w(to_le_bytes to_be_bytes from_le_bytes from_be_bytes),
         %{"Scalar" => %{"Integer" => integer}} = scalar <- CallModels.expand(parent, refs),
         [{signed, name}] <- Map.to_list(integer),
         {:ok, width} <- Map.fetch(@widths, {signed, name}),
         true <- signature?(sig, refs, method, scalar, byte_array(width)) do
      %{
        rust_name: "core::num::{#{String.downcase(name)}}::#{method}",
        lean: "Aeneas.Std.core.num.#{name}.#{method}",
        builtin: true,
        can_fail: false,
        lift: true,
        label: "Aeneas fixed-width endian conversion model; Rust core implementation not verified"
      }
    else
      _ -> nil
    end
  end

  defp empty_parameters?(%{
         "regions" => [],
         "types" => [],
         "const_generics" => [],
         "trait_clauses" => [],
         "outlives" => [],
         "trait_type_constraints" => []
       }),
       do: true

  defp empty_parameters?(_), do: false

  defp byte_array(width) do
    %{
      "Array" => [
        %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}},
        [
          %{"Integer" => %{"Unsigned" => ["Usize", Integer.to_string(width)]}},
          %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
        ],
        nil
      ]
    }
  end

  defp signature?(sig, refs, "to_" <> _, scalar, array),
    do:
      CallModels.expand(sig["inputs"], refs) == [scalar] and
        CallModels.expand(sig["output"], refs) == array

  defp signature?(sig, refs, "from_" <> _, scalar, array),
    do:
      CallModels.expand(sig["inputs"], refs) == [array] and
        CallModels.expand(sig["output"], refs) == scalar
end
