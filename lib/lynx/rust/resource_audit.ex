defmodule Lynx.Rust.ResourceAudit do
  @moduledoc false
  alias Lynx.Rust.{CallModels, NativeDrops, ResourceModels}

  def audit(functions, models, translated, refs) do
    ctx = %{
      translated: translated,
      refs: refs,
      traits: ResourceModels.trait_references(translated)
    }

    Enum.reduce_while(functions, :ok, fn f, :ok ->
      try do
        calls!(f["body"], models, ctx)
        {:cont, :ok}
      rescue
        e in ArgumentError -> {:halt, {:error, f, Exception.message(e)}}
      end
    end)
  end

  defp calls!(%{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => args}}, models, ctx) do
    if model = models[id] do
      if model[:resource_operation] do
        with %{
               "types" => [payload],
               "regions" => regions,
               "const_generics" => [],
               "trait_refs" => [dict]
             } <- args,
             true <- valid_regions?(regions, model.resource_operation),
             true <-
               payload?(payload, dict, model.resource_trait, ctx.translated, ctx.refs, ctx.traits) do
          :ok
        else
          _ ->
            raise ArgumentError,
                  "resource call requires a concrete default Resource implementation with a compiler-certified destructor-free payload or an extracted owning destructor"
        end
      end
    end
  end

  defp calls!(map, models, ctx) when is_map(map),
    do: Enum.each(Map.values(map), &calls!(&1, models, ctx))

  defp calls!(list, models, ctx) when is_list(list), do: Enum.each(list, &calls!(&1, models, ctx))
  defp calls!(_, _, _), do: :ok

  defp valid_regions?([], "new"), do: true
  defp valid_regions?([%{"Body" => n}], method) when method in ~w(clone deref), do: is_integer(n)
  defp valid_regions?(_, _), do: false

  def payload?(payload, dictionary, trait, translated, refs, traits) do
    payload = CallModels.expand(payload, refs)

    with true <-
           NativeDrops.destructor_free?(payload, translated, refs) or
             Lynx.Rust.NativeOwnedDrops.function_for(payload, translated, refs) != nil,
         %{"Adt" => %{"id" => type, "builtin" => nil, "generics" => empty}} <- payload,
         true <- empty == ResourceModels.args([]),
         %{
           "kind" => %{"TraitImpl" => %{"id" => impl_id, "generics" => args}},
           "trait_decl_ref" => decl
         } <-
           ResourceModels.dictionary(dictionary, traits),
         true <- args == ResourceModels.args([]),
         true <-
           CallModels.expand(decl, refs) == %{
             "id" => trait,
             "generics" => ResourceModels.args([payload])
           },
         impl when not is_nil(impl) <- find(translated["trait_impls"], impl_id),
         true <- default_impl?(impl, payload, trait, translated, refs, traits),
         declaration when not is_nil(declaration) <- find(translated["type_decls"], type),
         true <- declaration["src"] == "Normal" do
      true
    else
      _ -> false
    end
  end

  defp default_impl?(impl, payload, trait, translated, refs, traits) do
    empty = %{
      "regions" => [],
      "types" => [],
      "const_generics" => [],
      "trait_clauses" => [],
      "trait_type_constraints" => [],
      "outlives" => []
    }

    with %{
           "src" => "Normal",
           "is_negative" => false,
           "is_unsafe" => false,
           "methods" => [nil, nil],
           "types" => [],
           "consts" => constants
         } <- impl,
         true <- impl["generics"] == empty,
         true <-
           CallModels.expand(impl["impl_trait"], refs) == %{
             "id" => trait,
             "generics" => ResourceModels.args([payload])
           },
         true <- length(constants) == 2 do
      Enum.all?(Enum.with_index(constants), fn {constant, index} ->
        default_constant?(
          constant,
          index,
          impl["def_id"],
          payload,
          trait,
          translated,
          refs,
          traits
        )
      end)
    else
      _ -> false
    end
  end

  # The two foreign default flags are explicit Rustler 0.39 models, not assumed
  # first-party constants. A user override has a different source and is rejected.
  defp default_constant?(
         %{"id" => id, "generics" => args},
         index,
         impl,
         payload,
         trait,
         t,
         refs,
         traits
       ) do
    expected_name =
      path(~w(rustler resource traits Resource)) ++
        path([Enum.at(~w(IMPLEMENTS_DESTRUCTOR IMPLEMENTS_DOWN), index)])

    with %{"types" => [_], "regions" => [], "const_generics" => [], "trait_refs" => [dictionary]} <-
           args,
         true <- CallModels.expand(args["types"], refs) == [payload],
         %{
           "kind" => %{"TraitImpl" => %{"id" => ^impl, "generics" => actual}},
           "trait_decl_ref" => decl
         } <-
           ResourceModels.dictionary(dictionary, traits),
         true <- actual == ResourceModels.args([]),
         true <-
           CallModels.expand(decl, refs) == %{
             "id" => trait,
             "generics" => ResourceModels.args([payload])
           },
         global when not is_nil(global) <- find(t["global_decls"], id),
         true <-
           global["global_kind"] == "NamedConst" and global["item_meta"]["name"] == expected_name,
         true <- CallModels.expand(global["ty"], refs) == %{"Scalar" => "Bool"},
         %{"TraitDefault" => %{"item_id" => ^index, "trait_ref" => source}} <- global["src"],
         true <-
           CallModels.expand(source, refs) == %{
             "id" => trait,
             "generics" => ResourceModels.args([%{"TypeVar" => %{"Free" => 0}}])
           } do
      true
    else
      _ -> false
    end
  end

  defp default_constant?(_, _, _, _, _, _, _, _), do: false
  defp path(names), do: Enum.map(names, &%{"Ident" => [&1, 0]})
  defp find(values, id), do: Enum.find(values, &(&1 && &1["def_id"] == id))
end
