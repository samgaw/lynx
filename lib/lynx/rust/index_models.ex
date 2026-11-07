defmodule Lynx.Rust.IndexModels do
  @moduledoc false
  alias Lynx.Rust.CallModels

  # These standard wrappers retain their delegated trait dictionary in Aeneas;
  # they do not replace arbitrary indexing implementations with direct lookup.
  def resolve(function, translated, refs) do
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
               %{"Ident" => ["core", 0]},
               %{"Ident" => [container, 0]},
               %{"Impl" => %{"Trait" => impl_id}},
               %{"Ident" => ["index", 0]}
             ]
           }
         } <- function,
         true <- container in ~w(array slice),
         impl when not is_nil(impl) <-
           Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == impl_id)),
         decl when not is_nil(decl) <-
           Enum.find(translated["trait_decls"], &(&1 && &1["def_id"] == trait)),
         true <- decl["item_meta"]["name"] == name(~w(core ops index Index)),
         true <-
           impl["src"] == "Normal" and impl["is_unsafe"] == false and impl["is_negative"] == false do
      [t, i, o] = Enum.map(0..2, &%{"TypeVar" => %{"Free" => &1}})
      usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
      n = [%{"Var" => %{"Free" => 0}}, usize]
      slice = %{"Slice" => [t, nil]}
      parent = if container == "array", do: %{"Array" => [t, n, nil]}, else: slice
      consts = if container == "array", do: [%{"index" => 0, "ty" => usize}], else: []
      clause_types = if container == "array", do: [slice, i, o], else: [i, slice, o]

      clause_name =
        if container == "array",
          do: ~w(core ops index Index),
          else: ~w(core slice index SliceIndex)

      expanded = CallModels.expand(params, refs)
      impl_params = CallModels.expand(impl["generics"], refs)
      ref = fn type -> %{"Ref" => [%{"Var" => %{"Free" => 0}}, type, "Shared"]} end

      if parameters?(expanded, consts, 1, clause_types, clause_name, translated) and
           parameters?(impl_params, consts, 0, clause_types, clause_name, translated) and
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
        rust_type = if container == "array", do: "[@T; @N]", else: "[@T]"

        %{
          rust_name: "core::#{container}::{core::ops::index::Index<#{rust_type}, @I, @O>}::index",
          lean:
            "Aeneas.Std.core.#{container}.#{if container == "array", do: "Array", else: "Slice"}.index",
          builtin: true,
          can_fail: true,
          lift: true,
          label:
            "Aeneas standard #{container} Index wrapper with retained delegated trait dispatch and bounds panics; Rust core implementation not verified"
        }
      end
    else
      _ -> nil
    end
  end

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
         translated
       ) do
    region_ok = if count == 0, do: regions == [], else: match?([%{"index" => 0}], regions)

    bounds =
      for index <- [0, 2, 1],
          do: %{
            "regions" => [],
            "outlives" => [],
            "skip_binder" => [
              %{"Lub" => %{"TypeVar" => %{"Free" => index}}},
              %{"Var" => %{"Free" => 0}}
            ]
          }

    region_ok and Enum.map(consts, &Map.take(&1, ["index", "ty"])) == expected_consts and
      Enum.map(types, & &1["index"]) == [0, 1, 2] and
      outlives == if(count == 0, do: [], else: bounds) and args == args(clause_types) and
      Enum.any?(
        translated["trait_decls"],
        &(&1 && &1["def_id"] == id && &1["item_meta"]["name"] == name(clause_name))
      )
  end

  defp parameters?(_, _, _, _, _, _), do: false

  defp args(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp name(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
end
