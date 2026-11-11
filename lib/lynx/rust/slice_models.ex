defmodule Lynx.Rust.SliceModels do
  @moduledoc false
  alias Lynx.Rust.CallModels

  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "signature" => %{"is_unsafe" => false, "abi" => "Rust", "is_variadic" => false} = sig,
           "generics" => params
         } <- function,
         true <- parameters?(CallModels.expand(params, refs)) do
      t = %{"TypeVar" => %{"Free" => 0}}
      slice = %{"Slice" => [t, nil]}
      shared = %{"Ref" => [%{"Var" => %{"Free" => 0}}, slice, "Shared"]}
      mutable = %{"Ref" => [%{"Var" => %{"Free" => 0}}, slice, "Mut"]}
      usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
      inputs = CallModels.expand(sig["inputs"], refs)
      output = CallModels.expand(sig["output"], refs)
      name = function["item_meta"]["name"]
      range_to = range_to_type(translated, refs, usize)

      cond do
        range_to != nil and inputs == [range_to, shared] and
          option_reference?(output, slice, translated, refs) and
            index_identity?(function, translated, refs, t, slice, range_to, "get", 0, slice) ->
          model(
            "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get",
            "Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.get"
          )

        inherent?(name, slice, refs, "is_empty") and inputs == [shared] and
          output == %{"Scalar" => "Bool"} and function["src"] == "Normal" ->
          model("core::slice::{[@T]}::is_empty", "Aeneas.Std.core.slice.Slice.is_empty")
          |> Map.put(:lift, false)

        inherent?(name, slice, refs) and inputs == [shared, usize] and
          tuple?(output, [shared, shared]) and function["src"] == "Normal" ->
          model("core::slice::{[@T]}::split_at", "Aeneas.Std.core.slice.Slice.split_at")

        inputs == [usize, shared] and option_reference?(output, t, translated, refs) and
            index_identity?(function, translated, refs, t, slice, usize, "get", 0) ->
          model(
            "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::get",
            "Aeneas.Std.core.slice.index.Usize.get"
          )

        inputs == [usize, shared] and
          output == %{"Ref" => [%{"Var" => %{"Free" => 0}}, t, "Shared"]} and
            index_identity?(function, translated, refs, t, slice, usize, "index", 4) ->
          model(
            "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::index",
            "Aeneas.Std.core.slice.index.Usize.index"
          )

        inputs == [usize, mutable] and
          output == %{"Ref" => [%{"Var" => %{"Free" => 0}}, t, "Mut"]} and
            index_identity?(function, translated, refs, t, slice, usize, "index_mut", 5) ->
          model(
            "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::index_mut",
            "Aeneas.Std.core.slice.index.Usize.index_mut"
          )

        true ->
          nil
      end
    else
      _ -> nil
    end
  end

  defp option_reference?(
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}},
         t,
         translated,
         refs
       ) do
    type = Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id))

    type != nil and Lynx.Rust.OptionModels.option_type?(type, refs) and
      args == arguments([%{"Ref" => [%{"Var" => %{"Free" => 0}}, t, "Shared"]}])
  end

  defp option_reference?(_, _, _, _), do: false

  defp model(rust, lean),
    do: %{
      rust_name: rust,
      lean: lean,
      builtin: true,
      can_fail: true,
      lift: true,
      label:
        "Aeneas safe slice model preserving bounds panics and mutable updates; Rust core implementation not verified"
    }

  defp parameters?(%{
         "regions" => [%{"index" => 0}],
         "types" => [%{"index" => 0}],
         "const_generics" => [],
         "trait_clauses" => [],
         "trait_type_constraints" => [],
         "outlives" => outlives
       }),
       do:
         outlives in [
           [],
           [
             %{
               "regions" => [],
               "outlives" => [],
               "skip_binder" => [
                 %{"Lub" => %{"TypeVar" => %{"Free" => 0}}},
                 %{"Var" => %{"Free" => 0}}
               ]
             }
           ]
         ]

  defp parameters?(_), do: false

  defp inherent?(name, slice, refs, method \\ "split_at")

  defp inherent?(
         [
           %{"Ident" => ["core", 0]},
           %{"Ident" => ["slice", 0]},
           %{"Impl" => %{"Ty" => %{"skip_binder" => parent}}},
           %{"Ident" => [method, 0]}
         ],
         slice,
         refs,
         method
       ) do
    parent |> CallModels.expand(refs) |> free() == slice
  end

  defp inherent?(_, _, _, _), do: false

  defp free(%{"Bound" => [0, index]}), do: %{"Free" => index}
  defp free(map) when is_map(map), do: Map.new(map, fn {k, v} -> {k, free(v)} end)
  defp free(list) when is_list(list), do: Enum.map(list, &free/1)
  defp free(value), do: value

  defp tuple?(%{"Adt" => %{"builtin" => "Tuple", "generics" => args}}, fields),
    do: args == arguments(fields)

  defp tuple?(_, _), do: false

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp index_identity?(
         function,
         translated,
         refs,
         t,
         slice,
         index,
         method_name,
         method_index,
         output \\ nil
       ) do
    output = output || t
    id = function["def_id"]

    with %{
           "TraitImpl" => %{
             "impl_ref" => %{"id" => impl_id, "generics" => impl_args},
             "trait_ref" => %{"id" => trait, "generics" => trait_args},
             "item_id" => ^method_index,
             "reuses_default" => false
           }
         } <- function["src"],
         impl when not is_nil(impl) <-
           Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == impl_id)),
         decl when not is_nil(decl) <-
           Enum.find(translated["trait_decls"], &(&1 && &1["def_id"] == trait)) do
      name = [%{"Ident" => ["core", 0]}, %{"Ident" => ["slice", 0]}, %{"Ident" => ["index", 0]}]

      function["item_meta"]["name"] ==
        name ++ [%{"Impl" => %{"Trait" => impl_id}}, %{"Ident" => [method_name, 0]}] and
        decl["item_meta"]["name"] == name ++ [%{"Ident" => ["SliceIndex", 0]}] and
        impl["src"] == "Normal" and impl["is_negative"] == false and
        impl["is_unsafe"] == true and decl["is_unsafe"] == true and
        impl["types"] == [nil] and impl["consts"] == [] and impl["implied_trait_refs"] == [] and
        impl_parameters?(impl["generics"]) and
        CallModels.expand(impl_args, refs) == arguments([t]) and
        CallModels.expand(trait_args, refs) == arguments([index, slice, output]) and
        CallModels.expand(impl["impl_trait"], refs) == %{
          "id" => trait,
          "generics" => arguments([index, slice, output])
        } and
        case Enum.filter(
               impl["methods"],
               &(&1["kind"] == %{"TraitMethod" => [trait, method_index]})
             ) do
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

  # Retain and check the compiler's actual nominal range definition. The model
  # is selected by structure and identity, never by a user type's short name.
  defp range_to_type(translated, refs, usize) do
    Enum.find_value(translated["type_decls"], fn
      %{
        "def_id" => id,
        "src" => "Normal",
        "item_meta" => %{"name" => name},
        "generics" => params,
        "kind" => %{"Struct" => [%{"name" => "end", "ty" => field}]}
      } ->
        if name == Enum.map(~w(core ops range RangeTo), &%{"Ident" => [&1, 0]}) and
             impl_parameters?(params) and
             CallModels.expand(field, refs) == %{"TypeVar" => %{"Free" => 0}} do
          %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => arguments([usize])}}
        end

      _ ->
        nil
    end)
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
