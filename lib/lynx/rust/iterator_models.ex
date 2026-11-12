defmodule Lynx.Rust.IteratorModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, ResourceModels}

  # These are the shared-slice primitives already modeled by Aeneas. Custom
  # iterators retain their first-party bodies and never match these identities.
  def resolve(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => %{"TraitImpl" => source},
           "signature" => %{"is_unsafe" => false, "abi" => "Rust", "is_variadic" => false} = sig
         } <- function,
         false <- source["reuses_default"],
         0 <- source["item_id"],
         impl when not is_nil(impl) <- find(translated["trait_impls"], source["impl_ref"]["id"]),
         true <-
           impl["src"] == "Normal" and impl["is_unsafe"] == false and impl["is_negative"] == false,
         trait when not is_nil(trait) <- find(translated["trait_decls"], impl["impl_trait"]["id"]),
         true <- trait["src"] == "Normal" and trait["is_unsafe"] == false,
         true <- source["trait_ref"]["id"] == trait["def_id"],
         true <- impl["consts"] == [] and Enum.all?(impl["types"], &is_nil/1),
         true <-
           CallModels.expand(source["impl_ref"]["generics"], refs) ==
             arguments([variable()], [region(0)]),
         true <-
           CallModels.expand(source["trait_ref"]["generics"], refs) ==
             CallModels.expand(impl["impl_trait"]["generics"], refs),
         true <-
           function["item_meta"]["name"] == impl["item_meta"]["name"] ++ [ident(method(function))],
         true <-
           impl["item_meta"]["name"] ==
             path(~w(core slice iter)) ++ [%{"Impl" => %{"Trait" => impl["def_id"]}}],
         method when is_map(method) <- Enum.at(impl["methods"], 0),
         true <- method["kind"] == %{"TraitMethod" => [trait["def_id"], 0]},
         true <- method["skip_binder"]["id"] == function["def_id"],
         true <- forwarding?(method, method(function), refs),
         iterator when not is_nil(iterator) <-
           Enum.find(
             translated["type_decls"],
             &(&1 && &1["item_meta"]["name"] == path(~w(core slice iter Iter)))
           ),
         true <- iterator["kind"] == "Opaque" and iterator["src"] == "Normal",
         true <-
           params?(
             iterator["generics"],
             1,
             [bound(variable(), region(0)), bound(variable(), region(0))],
             refs
           ),
         true <- params?(impl["generics"], 1, [bound(variable(), region(0))], refs) do
      iter = adt(iterator["def_id"], [variable()], [region(0)])
      slice = reference(%{"Slice" => [variable(), nil]}, 0, "Shared")
      item = reference(variable(), 0, "Shared")
      inputs = CallModels.expand(sig["inputs"], refs)
      output = CallModels.expand(sig["output"], refs)
      implemented = CallModels.expand(impl["impl_trait"]["generics"], refs)

      cond do
        method(function) == "into_iter" and
          trait["item_meta"]["name"] == path(~w(core iter traits collect IntoIterator)) and
          trait_params?(trait["generics"], 3) and
          params?(function["generics"], 1, [bound(variable(), region(0))], refs) and
          inputs == [slice] and output == iter and implemented == arguments([slice, item, iter]) and
            next_dependency?(impl, translated, refs, iter) ->
          model(
            "into_iter",
            "SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter",
            "core::slice::iter::{core::iter::traits::collect::IntoIterator<&'a [@T], &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"
          )

        method(function) == "next" and
          trait["item_meta"]["name"] == path(~w(core iter traits iterator Iterator)) and
          trait_params?(trait["generics"], 2) and
          params?(
            function["generics"],
            2,
            [
              bound(variable(), region(0)),
              bound(region(0), region(1)),
              bound(variable(), region(1))
            ],
            refs
          ) and
          inputs == [reference(iter, 1, "Mut")] and option?(output, item, translated, refs) and
          implemented == arguments([iter, item]) and impl["implied_trait_refs"] == [] ->
          model(
            "next",
            "core.slice.iter.IteratorSliceIter.next",
            "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::next"
          )

        true ->
          nil
      end
    else
      _ -> nil
    end
  end

  defp forwarding?(method, name, refs) do
    count = if name == "next", do: 1, else: 0
    params = method["params"]

    bounds =
      if name == "next", do: [region(0), %{"Var" => %{"Bound" => [0, 0]}}], else: [region(0)]

    params["types"] == [] and params["const_generics"] == [] and params["outlives"] == [] and
      params["trait_clauses"] == [] and params["trait_type_constraints"] == [] and
      length(params["regions"]) == count and
      Enum.all?(params["regions"], &(&1["index"] == 0 and &1["late_bound"] == true)) and
      CallModels.expand(method["skip_binder"]["generics"], refs) ==
        arguments([variable()], bounds)
  end

  defp next_dependency?(impl, translated, refs, iter) do
    with [reference] <- CallModels.expand(impl["implied_trait_refs"], refs),
         %{"regions" => [], "outlives" => [], "skip_binder" => selected} <- reference,
         %{"TraitImpl" => next} <- selected["kind"],
         true <- CallModels.expand(next["generics"], refs) == arguments([variable()], ["Erased"]),
         next_impl when not is_nil(next_impl) <- find(translated["trait_impls"], next["id"]),
         true <- selected["trait_decl_ref"]["id"] == next_impl["impl_trait"]["id"],
         true <-
           CallModels.expand(selected["trait_decl_ref"]["generics"], refs) ==
             arguments([iter, %{"Ref" => ["Erased", variable(), "Shared"]}]),
         method when is_map(method) <- Enum.at(next_impl["methods"], 0),
         function when not is_nil(function) <-
           find(translated["fun_decls"], method["skip_binder"]["id"]),
         %{slice_iterator: "next"} <- resolve(function, translated, refs) do
      true
    else
      _ -> false
    end
  end

  defp model(method, lean, rust) do
    %{
      rust_name: rust,
      lean: "Aeneas.Std." <> lean,
      builtin: true,
      can_fail: true,
      lift: false,
      slice_iterator: method,
      label:
        "Aeneas shared-slice iterator model retaining the original slice and cursor, exhaustion and borrow update; Rust core iterator implementation and native pointer layout not verified"
    }
  end

  defp option?(
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}},
         item,
         translated,
         refs
       ) do
    args == arguments([item]) and
      case find(translated["type_decls"], id) do
        %{
          "item_meta" => %{"name" => name},
          "kind" => %{"Enum" => [none, some]},
          "generics" => params
        } ->
          name == path(~w(core option Option)) and params?(params, 0, [], refs) and
            Map.take(none, ["id", "name", "fields", "discriminant"]) == %{
              "id" => 0,
              "name" => "None",
              "fields" => [],
              "discriminant" => %{"Signed" => ["Isize", "0"]}
            } and
            Map.take(some, ["id", "name", "discriminant"]) == %{
              "id" => 1,
              "name" => "Some",
              "discriminant" => %{"Signed" => ["Isize", "1"]}
            } and
            match?([%{"ty" => _}], some["fields"]) and
            CallModels.expand(hd(some["fields"])["ty"], refs) == variable()

        _ ->
          false
      end
  end

  defp option?(_, _, _, _), do: false

  defp params?(params, count, bounds, refs),
    do: ResourceModels.params?(CallModels.expand(params, refs), count, [], bounds)

  defp trait_params?(
         %{
           "regions" => [],
           "const_generics" => [],
           "trait_clauses" => [],
           "outlives" => [],
           "trait_type_constraints" => [],
           "types" => types
         },
         count
       ),
       do: Enum.map(types, & &1["index"]) == Enum.to_list(0..(count - 1))

  defp trait_params?(_, _), do: false
  defp method(function), do: List.last(function["item_meta"]["name"])["Ident"] |> List.first()
  defp find(items, id), do: Enum.find(items, &(&1 && &1["def_id"] == id))
  defp ident(name), do: %{"Ident" => [name, 0]}
  defp path(parts), do: Enum.map(parts, &ident/1)
  defp variable, do: %{"TypeVar" => %{"Free" => 0}}
  defp region(index), do: %{"Var" => %{"Free" => index}}
  defp reference(type, region, mutability), do: %{"Ref" => [region(region), type, mutability]}
  defp arguments(types, regions \\ []), do: ResourceModels.args(types, [], regions)

  defp adt(id, types, regions),
    do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => arguments(types, regions)}}

  defp bound(left, right),
    do: %{
      "regions" => [],
      "outlives" => [],
      "skip_binder" => [
        if(match?(%{"TypeVar" => _}, left), do: %{"Lub" => left}, else: left),
        right
      ]
    }
end
