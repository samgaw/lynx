defmodule Lynx.Rust.SliceModels do
  @moduledoc false
  alias Lynx.Rust.CallModels

  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "signature" => %{"is_unsafe" => false, "abi" => "Rust", "is_variadic" => false} = sig,
           "generics" => params
         } <- function,
         true <- parameters?(params) do
      t = %{"TypeVar" => %{"Free" => 0}}
      slice = %{"Slice" => [t, nil]}
      shared = %{"Ref" => [%{"Var" => %{"Free" => 0}}, slice, "Shared"]}
      usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
      inputs = CallModels.expand(sig["inputs"], refs)
      output = CallModels.expand(sig["output"], refs)
      name = function["item_meta"]["name"]

      cond do
        inherent?(name, slice, refs) and inputs == [shared, usize] and
          tuple?(output, [shared, shared]) and function["src"] == "Normal" ->
          model("core::slice::{[@T]}::split_at", "Aeneas.Std.core.slice.Slice.split_at")

        inputs == [usize, shared] and
          output == %{"Ref" => [%{"Var" => %{"Free" => 0}}, t, "Shared"]} and
            index_identity?(function, translated, refs, t, slice, usize) ->
          model(
            "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::index",
            "Aeneas.Std.core.slice.index.Usize.index"
          )

        true ->
          nil
      end
    else
      _ -> nil
    end
  end

  defp model(rust, lean),
    do: %{
      rust_name: rust,
      lean: lean,
      builtin: true,
      can_fail: true,
      lift: true,
      label:
        "Aeneas safe shared-slice model with bounds panic; Rust core implementation not verified"
    }

  defp parameters?(%{
         "regions" => [%{"index" => 0}],
         "types" => [%{"index" => 0}],
         "const_generics" => [],
         "trait_clauses" => [],
         "trait_type_constraints" => []
       }),
       do: true

  defp parameters?(_), do: false

  defp inherent?(
         [
           %{"Ident" => ["core", 0]},
           %{"Ident" => ["slice", 0]},
           %{"Impl" => %{"Ty" => %{"skip_binder" => parent}}},
           %{"Ident" => ["split_at", 0]}
         ],
         slice,
         refs
       ) do
    parent |> CallModels.expand(refs) |> free() == slice
  end

  defp inherent?(_, _, _), do: false

  defp free(%{"Bound" => [0, index]}), do: %{"Free" => index}
  defp free(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, free(v)} end)
  defp free(list) when is_list(list), do: Enum.map(list, &free/1)
  defp free(value), do: value

  defp tuple?(%{"Adt" => %{"builtin" => "Tuple", "generics" => args}}, fields),
    do: args == arguments(fields)

  defp tuple?(_, _), do: false

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp index_identity?(function, translated, refs, t, slice, usize) do
    id = function["def_id"]

    with %{
           "TraitImpl" => %{
             "impl_ref" => %{"id" => impl_id, "generics" => impl_args},
             "trait_ref" => %{"id" => trait, "generics" => trait_args},
             "item_id" => 4,
             "reuses_default" => false
           }
         } <- function["src"],
         impl when not is_nil(impl) <-
           Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == impl_id)),
         decl when not is_nil(decl) <-
           Enum.find(translated["trait_decls"], &(&1 && &1["def_id"] == trait)) do
      name = [%{"Ident" => ["core", 0]}, %{"Ident" => ["slice", 0]}, %{"Ident" => ["index", 0]}]

      function["item_meta"]["name"] ==
        name ++ [%{"Impl" => %{"Trait" => impl_id}}, %{"Ident" => ["index", 0]}] and
        decl["item_meta"]["name"] == name ++ [%{"Ident" => ["SliceIndex", 0]}] and
        impl["src"] == "Normal" and impl["is_negative"] == false and
        impl["is_unsafe"] == true and decl["is_unsafe"] == true and
        impl["types"] == [nil] and impl["consts"] == [] and impl["implied_trait_refs"] == [] and
        impl_parameters?(impl["generics"]) and
        CallModels.expand(impl_args, refs) == arguments([t]) and
        CallModels.expand(trait_args, refs) == arguments([usize, slice, t]) and
        CallModels.expand(impl["impl_trait"], refs) == %{
          "id" => trait,
          "generics" => arguments([usize, slice, t])
        } and
        case Enum.filter(impl["methods"], &(&1["kind"] == %{"TraitMethod" => [trait, 4]})) do
          [%{"params" => method_params, "skip_binder" => %{"id" => ^id, "generics" => args}}] ->
            method_parameters?(method_params) and
              CallModels.expand(args, refs) ==
                Map.put(arguments([t]), "regions", [%{"Var" => %{"Bound" => [0, 0]}}])

          _ ->
            false
        end
    else
      _ -> false
    end
  end

  defp impl_parameters?(%{
         "regions" => [],
         "types" => [%{"index" => 0}],
         "const_generics" => [],
         "trait_clauses" => [],
         "outlives" => [],
         "trait_type_constraints" => []
       }),
       do: true

  defp impl_parameters?(_), do: false

  defp method_parameters?(%{
         "regions" => [%{"index" => 0}],
         "types" => [],
         "const_generics" => [],
         "trait_clauses" => [],
         "outlives" => [],
         "trait_type_constraints" => []
       }),
       do: true

  defp method_parameters?(_), do: false
end
