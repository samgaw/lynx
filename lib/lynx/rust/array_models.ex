defmodule Lynx.Rust.ArrayModels do
  @moduledoc false
  alias Lynx.Rust.CallModels

  def resolve(function, _translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "generics" => params,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["core", 0]},
               %{"Ident" => ["array", 0]},
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
         true <- method in ~w(as_slice as_mut_slice),
         true <- parameters?(CallModels.expand(params, refs), 1),
         true <- parameters?(CallModels.expand(parent_params, refs), 0) do
      t = %{"TypeVar" => %{"Free" => 0}}
      usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
      array = %{"Array" => [t, [%{"Var" => %{"Free" => 0}}, usize], nil]}
      slice = %{"Slice" => [t, nil]}
      mutability = if method == "as_mut_slice", do: "Mut", else: "Shared"
      reference = fn type -> %{"Ref" => [%{"Var" => %{"Free" => 0}}, type, mutability]} end

      if free(CallModels.expand(parent, refs)) == array and
           CallModels.expand(sig["inputs"], refs) == [reference.(array)] and
           CallModels.expand(sig["output"], refs) == reference.(slice) do
        %{
          rust_name: "core::array::{[@T; @N]}::" <> method,
          lean:
            "Aeneas.Std.Array." <>
              if(method == "as_mut_slice", do: "to_slice_mut", else: "to_slice"),
          builtin: true,
          can_fail: false,
          lift: true,
          label:
            "Aeneas array slice-view model preserving length and mutable reconstruction; Rust core implementation not verified"
        }
      end
    else
      _ -> nil
    end
  end

  defp parameters?(
         %{
           "regions" => regions,
           "types" => [%{"index" => 0}],
           "const_generics" => [
             %{"index" => 0, "ty" => %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}}
           ],
           "trait_clauses" => [],
           "trait_type_constraints" => [],
           "outlives" => outlives
         },
         count
       ) do
    regions_ok = if count == 0, do: regions == [], else: match?([%{"index" => 0}], regions)

    regions_ok and
      (outlives == [] or
         (count == 1 and
            outlives == [
              %{
                "regions" => [],
                "outlives" => [],
                "skip_binder" => [
                  %{"Lub" => %{"TypeVar" => %{"Free" => 0}}},
                  %{"Var" => %{"Free" => 0}}
                ]
              }
            ]))
  end

  defp parameters?(_, _), do: false
  defp free(%{"Bound" => [0, index]}), do: %{"Free" => index}
  defp free(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, free(v)} end)
  defp free(list) when is_list(list), do: Enum.map(list, &free/1)
  defp free(value), do: value
end
