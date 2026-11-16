defmodule Lynx.Rust.ArrayModels do
  @moduledoc false
  alias Lynx.Rust.CallModels

  def resolve(function, translated, refs),
    do: repeat(function, translated, refs) || view(function, refs)

  defp repeat(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "generics" => params,
           "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false} = sig,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["core", 0]},
               %{"Ident" => ["array", 0]},
               %{"Ident" => ["repeat", 0]}
             ]
           }
         } <- function,
         params = CallModels.expand(params, refs),
         [%{"clause_id" => 0, "trait_" => clause}] <- params["trait_clauses"],
         true <- parameters?(%{params | "trait_clauses" => []}, 0),
         %{
           "regions" => [],
           "outlives" => [],
           "skip_binder" => %{"id" => trait, "generics" => args}
         } <- CallModels.expand(clause, refs),
         true <- args == Lynx.Rust.ResourceModels.args([%{"TypeVar" => %{"Free" => 0}}]),
         [declaration] <- Enum.filter(translated["trait_decls"], &(&1 && &1["def_id"] == trait)),
         true <- Lynx.Rust.VectorExtensions.clone_trait?(declaration, refs),
         variable = %{"TypeVar" => %{"Free" => 0}},
         usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}},
         true <- CallModels.expand(sig["inputs"], refs) == [variable],
         true <-
           CallModels.expand(sig["output"], refs) == %{
             "Array" => [variable, [%{"Var" => %{"Free" => 0}}, usize], nil]
           } do
      %{
        rust_name: "core::array::repeat",
        lean: "Aeneas.Std.Array.repeat",
        builtin: true,
        can_fail: false,
        lift: false,
        byte_array_repeat: true,
        label:
          "Upstream array repeat model restricted at every call to concrete u8 and the exact standard Clone<u8> dictionary; callback-free byte cloning and logical array length/content preserved; Rust core implementation, native storage and allocation failure are unverified; custom/effectful clones and non-byte elements are rejected"
      }
    else
      _ -> nil
    end
  end

  def repeat_call?(args, translated, refs) do
    case args do
      %{"regions" => [], "types" => [element], "const_generics" => [_], "trait_refs" => [dict]} ->
        CallModels.expand(element, refs) == %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}} and
          Lynx.Rust.VectorExtensions.valid_byte_clone?(dict, translated, refs)

      _ ->
        false
    end
  end

  defp view(function, refs) do
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
