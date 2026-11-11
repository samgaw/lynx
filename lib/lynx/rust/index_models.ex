defmodule Lynx.Rust.IndexModels do
  @moduledoc false
  alias Lynx.Rust.CallModels

  # These standard wrappers retain their delegated trait dictionary in Aeneas;
  # they do not replace arbitrary indexing implementations with direct lookup.
  def resolve(function, translated, refs),
    do: resolve_get(function, translated, refs) || resolve_index(function, translated, refs)

  # Resolve the method actually selected by Slice.get's dictionary. Reporting
  # only the generic wrapper would hide the external indexing implementation.
  def audit(functions, models, translated, refs) do
    traits = Lynx.Rust.ResourceModels.trait_references(translated)

    Enum.reduce_while(functions, {:ok, %{}}, fn function, {:ok, dependencies} ->
      try do
        ids = dispatches(function["body"], models, translated, refs, traits) |> Enum.uniq()
        {:cont, {:ok, Map.put(dependencies, function["def_id"], ids)}}
      rescue
        error in ArgumentError -> {:halt, {:error, function, Exception.message(error)}}
      end
    end)
  end

  defp dispatches(
         %{
           "Call" => %{
             "call" => %{
               "func" => %{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => args}}
             }
           }
         } = node,
         models,
         translated,
         refs,
         traits
       ) do
    selected =
      case models[id] do
        %{slice_index_method: index} ->
          [index_method!(args, index, models, translated, refs, traits)]

        _ ->
          []
      end

    selected ++ Enum.flat_map(Map.values(node), &dispatches(&1, models, translated, refs, traits))
  end

  defp dispatches(node, models, translated, refs, traits) when is_map(node),
    do: Enum.flat_map(Map.values(node), &dispatches(&1, models, translated, refs, traits))

  defp dispatches(nodes, models, translated, refs, traits) when is_list(nodes),
    do: Enum.flat_map(nodes, &dispatches(&1, models, translated, refs, traits))

  defp dispatches(_, _, _, _, _), do: []

  defp index_method!(args, index, models, translated, refs, traits) do
    with %{
           "regions" => [_],
           "types" => [element, input, output],
           "const_generics" => [],
           "trait_refs" => [ref]
         } <- args,
         %{"regions" => [], "outlives" => [], "skip_binder" => value} <- ref,
         %{
           "kind" => %{"TraitImpl" => %{"id" => impl_id, "generics" => actual}},
           "trait_decl_ref" => %{"id" => trait, "generics" => declared}
         } <- trait_value(value, traits),
         %{} = impl <- Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == impl_id)),
         true <- CallModels.expand(actual, refs) == args([CallModels.expand(element, refs)]),
         expected = args([input, %{"Slice" => [element, nil]}, output]) |> CallModels.expand(refs),
         true <- CallModels.expand(declared, refs) == expected,
         true <- impl["impl_trait"]["id"] == trait,
         true <-
           instantiate(
             CallModels.expand(impl["impl_trait"]["generics"], refs),
             CallModels.expand(element, refs)
           ) == expected,
         [%{"skip_binder" => %{"id" => method}}] <-
           Enum.filter(impl["methods"], &(&1["kind"] == %{"TraitMethod" => [trait, index]})),
         %{lean: lean} <- models[method],
         true <-
           lean in [
             "Aeneas.Std.core.slice.index.Usize.get",
             "Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.get",
             "Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.get",
             "Aeneas.Std.core.slice.index.SliceIndexRangeFromUsizeSlice.get"
           ] do
      method
    else
      _ ->
        raise ArgumentError,
              "missing or unsupported SliceIndex implementation selected by slice get"
    end
  end

  defp trait_value(%{"Value" => [_, value]}, _), do: value
  defp trait_value(%{"Deduplicated" => id}, refs), do: refs[id]
  defp trait_value(_, _), do: nil

  defp instantiate(%{"TypeVar" => %{"Free" => 0}}, element), do: element

  defp instantiate(map, element) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, instantiate(value, element)} end)

  defp instantiate(list, element) when is_list(list),
    do: Enum.map(list, &instantiate(&1, element))

  defp instantiate(value, _), do: value

  defp resolve_get(
         %{
           "body" => "Opaque",
           "src" => "Normal",
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["core", 0]},
               %{"Ident" => ["slice", 0]},
               %{"Impl" => %{"Ty" => parent}},
               %{"Ident" => ["get", 0]}
             ]
           },
           "signature" => sig,
           "generics" => params
         },
         translated,
         refs
       ) do
    [t, i, o] = Enum.map(0..2, &%{"TypeVar" => %{"Free" => &1}})
    slice = %{"Slice" => [t, nil]}
    ref = fn type -> %{"Ref" => [%{"Var" => %{"Free" => 0}}, type, "Shared"]} end

    with true <-
           parameters?(
             CallModels.expand(params, refs),
             [],
             1,
             [i, slice, o],
             ~w(core slice index SliceIndex),
             translated
           ),
         true <- parent["kind"] == "InherentImplBlock",
         true <-
           CallModels.expand(parent["skip_binder"], refs) == %{
             "Slice" => [%{"TypeVar" => %{"Bound" => [0, 0]}}, nil]
           },
         true <- simple_parent?(parent["params"]),
         %{
           "is_unsafe" => false,
           "abi" => "Rust",
           "is_variadic" => false,
           "inputs" => inputs,
           "output" => output
         } <- sig,
         true <- CallModels.expand(inputs, refs) == [ref.(slice), i],
         %{"Adt" => %{"builtin" => nil, "id" => option, "generics" => args}} <-
           CallModels.expand(output, refs),
         true <- args == args([ref.(o)]),
         type when not is_nil(type) <-
           Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == option)),
         true <- Lynx.Rust.OptionModels.option_type?(type, refs) do
      %{
        rust_name: "core::slice::{[@T]}::get",
        lean: "Aeneas.Std.core.slice.Slice.get",
        builtin: true,
        slice_index_method: 0,
        can_fail: true,
        lift: true,
        label:
          "Aeneas safe slice get wrapper retaining its actual SliceIndex dictionary and out-of-bounds None; Rust core implementation not verified"
      }
    else
      _ -> nil
    end
  end

  defp resolve_get(_, _, _), do: nil

  defp simple_parent?(%{
         "regions" => [],
         "types" => [%{"index" => 0}],
         "const_generics" => [],
         "trait_clauses" => [],
         "outlives" => [],
         "trait_type_constraints" => []
       }),
       do: true

  defp simple_parent?(_), do: false

  defp resolve_index(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "src" => %{
             "TraitImpl" => %{
               "impl_ref" => %{"id" => impl_id},
               "trait_ref" => %{"id" => trait},
               "item_id" => 0,
               "reuses_default" => false
             }
           },
           "generics" => params,
           "def_id" => id,
           "item_meta" => %{
             "name" => [
               %{"Ident" => [library, 0]},
               %{"Ident" => [container, 0]},
               %{"Impl" => %{"Trait" => impl_id}},
               %{"Ident" => ["index", 0]}
             ]
           }
         } <- function,
         true <- {library, container} in [{"core", "array"}, {"core", "slice"}, {"alloc", "vec"}],
         impl when not is_nil(impl) <-
           Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == impl_id)),
         decl when not is_nil(decl) <-
           Enum.find(translated["trait_decls"], &(&1 && &1["def_id"] == trait)),
         true <- decl["item_meta"]["name"] == name(~w(core ops index Index)),
         true <-
           impl["src"] == "Normal" and impl["is_unsafe"] == false and impl["is_negative"] == false do
      indices = if container == "vec", do: [0, 1, 2, 3], else: [0, 1, 2]
      t = %{"TypeVar" => %{"Free" => 0}}
      i = %{"TypeVar" => %{"Free" => 1}}
      o = %{"TypeVar" => %{"Free" => List.last(indices)}}
      usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
      n = [%{"Var" => %{"Free" => 0}}, usize]
      slice = %{"Slice" => [t, nil]}

      vector =
        Enum.find(
          translated["type_decls"],
          &(&1 && &1["item_meta"]["name"] == name(~w(alloc vec Vec)))
        )

      parent =
        case container do
          "array" ->
            %{"Array" => [t, n, nil]}

          "slice" ->
            slice

          "vec" ->
            %{
              "Adt" => %{
                "id" => vector && vector["def_id"],
                "builtin" => nil,
                "generics" => args([t])
              }
            }
        end

      consts = if container == "array", do: [%{"index" => 0, "ty" => usize}], else: []
      clause_types = if container == "array", do: [slice, i, o], else: [i, slice, o]

      clause_name =
        if container == "array",
          do: ~w(core ops index Index),
          else: ~w(core slice index SliceIndex)

      expanded = CallModels.expand(params, refs)
      impl_params = CallModels.expand(impl["generics"], refs)
      ref = fn type -> %{"Ref" => [%{"Var" => %{"Free" => 0}}, type, "Shared"]} end

      if (container != "vec" or (vector != nil and simple_parent?(vector["generics"]))) and
           parameters?(expanded, consts, 1, clause_types, clause_name, translated, indices) and
           parameters?(impl_params, consts, 0, clause_types, clause_name, translated, indices) and
           CallModels.expand(sig["inputs"], refs) == [ref.(parent), i] and
           CallModels.expand(sig["output"], refs) == ref.(o) and
           CallModels.expand(impl["impl_trait"], refs) == %{
             "id" => trait,
             "generics" => args([parent, i, o])
           } and
           Enum.count(
             impl["methods"],
             &match?(
               %{"kind" => %{"TraitMethod" => [^trait, 0]}, "skip_binder" => %{"id" => ^id}},
               &1
             )
           ) == 1 do
        rust_type =
          case container do
            "array" -> "[@T; @N]"
            "slice" -> "[@T]"
            "vec" -> "alloc::vec::Vec<@T>"
          end

        model = %{
          rust_name:
            "#{library}::#{container}::{core::ops::index::Index<#{rust_type}, @I, @O>}::index",
          lean:
            if(container == "vec",
              do: "Aeneas.Std.alloc.vec.Vec.index",
              else:
                "Aeneas.Std.core.#{container}.#{if container == "array", do: "Array", else: "Slice"}.index"
            ),
          builtin: true,
          can_fail: true,
          lift: true,
          label:
            "Aeneas standard #{container} Index wrapper with retained delegated trait dispatch and bounds panics; Rust core implementation not verified"
        }

        if container == "vec", do: Map.put(model, :vec_owned_method, "index"), else: model
      end
    else
      _ -> nil
    end
  end

  defp parameters?(
         params,
         expected_consts,
         count,
         clause_types,
         clause_name,
         translated,
         indices \\ [0, 1, 2]
       )

  defp parameters?(
         %{
           "regions" => regions,
           "types" => types,
           "const_generics" => consts,
           "trait_clauses" => [
             %{
               "clause_id" => 0,
               "trait_" => %{
                 "regions" => [],
                 "outlives" => [],
                 "skip_binder" => %{"id" => id, "generics" => args}
               }
             }
           ],
           "outlives" => outlives,
           "trait_type_constraints" => []
         },
         expected_consts,
         count,
         clause_types,
         clause_name,
         translated,
         indices
       ) do
    region_ok = if count == 0, do: regions == [], else: match?([%{"index" => 0}], regions)

    bounds =
      for index <- if(length(indices) == 4, do: [0, 2, 3, 1], else: [0, 2, 1]),
          do: %{
            "regions" => [],
            "outlives" => [],
            "skip_binder" => [
              %{"Lub" => %{"TypeVar" => %{"Free" => index}}},
              %{"Var" => %{"Free" => 0}}
            ]
          }

    region_ok and Enum.map(consts, &Map.take(&1, ["index", "ty"])) == expected_consts and
      Enum.map(types, & &1["index"]) == indices and
      outlives == if(count == 0, do: [], else: bounds) and args == args(clause_types) and
      Enum.any?(
        translated["trait_decls"],
        &(&1 && &1["def_id"] == id && &1["item_meta"]["name"] == name(clause_name))
      )
  end

  defp parameters?(_, _, _, _, _, _, _), do: false

  defp args(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp name(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
end
