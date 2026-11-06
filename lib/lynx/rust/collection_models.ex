defmodule Lynx.Rust.CollectionModels do
  @moduledoc false
  alias Lynx.Rust.CallModels

  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "generics" => params,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["alloc", 0]},
               %{"Ident" => ["vec", 0]},
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
         true <- parameters?(parent_params, 0),
         %{"Adt" => %{"builtin" => nil, "id" => id, "generics" => args}} = vector <-
           CallModels.expand(parent, refs) |> free(),
         true <- args == arguments([type_var(0)]),
         type when not is_nil(type) <-
           Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id)),
         true <- type["item_meta"]["name"] == path(~w(alloc vec Vec)),
         true <- type_parameters?(type["generics"]),
         mutability = if(method == "as_mut_slice", do: "Mut", else: "Shared"),
         true <- CallModels.expand(sig["inputs"], refs) == [reference(vector, mutability)],
         true <-
           CallModels.expand(sig["output"], refs) ==
             reference(%{"Slice" => [type_var(0), nil]}, mutability) do
      %{
        rust_name: "alloc::vec::{alloc::vec::Vec<@T>}::#{method}",
        lean:
          "Aeneas.Std.alloc.vec.Vec." <>
            if(method == "as_mut_slice", do: "deref_mut", else: "deref"),
        builtin: false,
        can_fail: false,
        lift: method == "as_mut_slice",
        keep_params: [true, false],
        label:
          "Aeneas Vec slice-view model preserving in-place updates; allocation and capacity are not observed; Rust alloc implementation not verified"
      }
    else
      _ -> nil
    end
  end

  defp type_parameters?(%{
         "regions" => [],
         "types" => [%{"index" => 0}],
         "const_generics" => [],
         "trait_clauses" => [],
         "trait_type_constraints" => [],
         "outlives" => []
       }),
       do: true

  defp type_parameters?(_), do: false

  defp parameters?(
         %{
           "regions" => regions,
           "types" => [%{"index" => 0}, %{"index" => 1}],
           "const_generics" => [],
           "trait_clauses" => [],
           "trait_type_constraints" => [],
           "outlives" => outlives
         },
         count
       ) do
    case count do
      0 ->
        regions == [] and outlives == []

      1 ->
        match?([%{"index" => 0}], regions) and
          outlives ==
            Enum.map(0..1, fn index ->
              %{
                "regions" => [],
                "outlives" => [],
                "skip_binder" => [%{"Lub" => type_var(index)}, %{"Var" => %{"Free" => 0}}]
              }
            end)
    end
  end

  defp parameters?(_, _), do: false

  defp reference(type, mutability), do: %{"Ref" => [%{"Var" => %{"Free" => 0}}, type, mutability]}

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp type_var(index), do: %{"TypeVar" => %{"Free" => index}}
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
  defp free(%{"Bound" => [0, index]}), do: %{"Free" => index}
  defp free(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, free(v)} end)
  defp free(list) when is_list(list), do: Enum.map(list, &free/1)
  defp free(value), do: value
end
