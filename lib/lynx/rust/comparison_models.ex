defmodule Lynx.Rust.ComparisonModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, ResourceModels}

  # These are the existing Aeneas comparison primitives, not contracts for
  # first-party comparators. Both methods must be captured: Slice.eq calls ne.
  def resolve(%{"body" => "Opaque", "signature" => sig} = f, t, refs) do
    with true <- safe?(sig),
         trait when not is_nil(trait) <- comparison_trait(t),
         {family, method, left, right, region, count} <- identity(f, trait, t, refs),
         true <- parameters?(f["generics"], count, region + 2, family != :scalar, trait),
         true <- family == :scalar or comparison_clause?(f["generics"], trait, refs),
         true <-
           CallModels.expand(sig["inputs"], refs) == [ref(left, region), ref(right, region + 1)],
         true <- CallModels.expand(sig["output"], refs) == %{"Scalar" => "Bool"} do
      {rust, lean} = names(family, method, left)

      %{
        rust_name: rust,
        lean: "Aeneas.Std." <> lean,
        builtin: true,
        can_fail: true,
        lift: false,
        comparison_trait: trait,
        comparison_family: family,
        label:
          "Aeneas PartialEq #{family} #{method} model with retained eq/ne dispatch and failures; Rust core implementation not verified"
      }
    else
      _ -> nil
    end
  end

  def resolve(_, _, _), do: nil

  def prefix_helper?(f, t) do
    refs = LLBC.type_references!(%{"translated" => t})
    trait = comparison_trait(t)

    with "Normal" <- f["src"],
         true <- safe?(f["signature"]),
         true <- is_integer(trait) and parameters?(f["generics"], 1, 2, true, trait),
         [clause] <- f["generics"]["trait_clauses"],
         true <-
           CallModels.expand(clause["trait_"]["skip_binder"], refs) ==
             declaration(trait, [var(0), var(0)]),
         true <-
           CallModels.expand(f["signature"]["inputs"], refs) == [
             ref(slice(var(0)), 0),
             ref(slice(var(0)), 1)
           ],
         true <- CallModels.expand(f["signature"]["output"], refs) == %{"Scalar" => "Bool"},
         %{"Ty" => %{"skip_binder" => parent, "params" => params}} <-
           Enum.at(f["item_meta"]["name"], 2)["Impl"] do
      parameters?(params, 1, 0, false, nil) and
        CallModels.expand(parent, refs) == slice(%{"TypeVar" => %{"Bound" => [0, 0]}})
    else
      _ -> false
    end
  end

  defp identity(f, trait, t, refs) do
    case f["src"] do
      %{"TraitDefault" => %{"trait_ref" => %{"id" => ^trait} = declared, "item_id" => 1}} ->
        if f["item_meta"]["name"] == path(~w(core cmp PartialEq ne)) and
             CallModels.expand(declared, refs) == declaration(trait, [var(0), var(1)]),
           do: {:default, "ne", var(0), var(1), 0, 2}

      %{
        "TraitImpl" => %{
          "impl_ref" => %{"id" => impl_id},
          "trait_ref" => %{"id" => ^trait},
          "item_id" => index,
          "reuses_default" => false
        }
      }
      when index in [0, 1] ->
        method = Enum.at(~w(eq ne), index)
        impl = find(t["trait_impls"], impl_id)

        with %{
               "src" => "Normal",
               "is_unsafe" => false,
               "is_negative" => false,
               "impl_trait" => %{"id" => ^trait, "generics" => g}
             } <- impl,
             %{"kind" => %{"TraitMethod" => [^trait, ^index]}, "skip_binder" => %{"id" => id}} <-
               Enum.at(impl["methods"], index),
             true <- id == f["def_id"],
             true <-
               CallModels.expand(f["src"]["TraitImpl"]["trait_ref"], refs) ==
                 CallModels.expand(impl["impl_trait"], refs),
             true <- g["regions"] == [] and g["const_generics"] == [] and g["trait_refs"] == [] do
          pair = CallModels.expand(g["types"], refs)
          name = f["item_meta"]["name"]

          cond do
            name ==
              path(~w(core cmp impls)) ++ [%{"Impl" => %{"Trait" => impl_id}}, ident(method)] and
              pair == [ref(var(0), 1), ref(var(1), 0)] and
              parameters?(impl["generics"], 2, 2, true, trait) and
                comparison_clause?(impl["generics"], trait, refs) ->
              {:shared, method, hd(pair), List.last(pair), 2, 2}

            name ==
              path(~w(core slice cmp)) ++ [%{"Impl" => %{"Trait" => impl_id}}, ident(method)] and
              pair == [slice(var(0)), slice(var(1))] and
              parameters?(impl["generics"], 2, 0, true, trait) and
                comparison_clause?(impl["generics"], trait, refs) ->
              {:slice, method, hd(pair), List.last(pair), 0, 2}

            name ==
              path(~w(core cmp impls)) ++ [%{"Impl" => %{"Trait" => impl_id}}, ident(method)] and
              scalar?(hd(pair)) and hd(pair) == List.last(pair) and
                parameters?(impl["generics"], 0, 0, false, trait) ->
              {:scalar, method, hd(pair), hd(pair), 0, 0}

            true ->
              nil
          end
        else
          _ -> nil
        end

      _ ->
        nil
    end
  end

  defp names(:shared, method, _),
    do:
      {"core::cmp::impls::{core::cmp::PartialEq<&'a @A, &'b @B>}::#{method}",
       "core.cmp.impls.PartialEqShared.#{method}"}

  defp names(:slice, method, _),
    do:
      {"core::slice::cmp::{core::cmp::PartialEq<[@T], [@U]>}::#{method}",
       "core.slice.cmp.PartialEqSlice.#{method}"}

  defp names(:default, "ne", _),
    do: {"core::cmp::PartialEq::ne", "core.cmp.PartialEq.ne.trait_default"}

  defp names(:scalar, method, %{"Scalar" => %{"Integer" => width}}) do
    [width] = Map.values(width)

    {"core::cmp::impls::{core::cmp::PartialEq<#{String.downcase(width)}, #{String.downcase(width)}>}::#{method}",
     "core.cmp.impls.PartialEq#{width}.#{method}"}
  end

  def audit(functions, models, t, refs) do
    ctx = %{
      functions: Map.new(functions, &{&1["def_id"], &1}),
      models: models,
      t: t,
      refs: refs,
      traits: ResourceModels.trait_references(t),
      trait: comparison_trait(t)
    }

    Enum.reduce_while(functions, {:ok, %{}}, fn f, {:ok, deps} ->
      try do
        ids = walk(f["body"], f, ctx) |> Enum.uniq()
        {:cont, {:ok, Map.put(deps, f["def_id"], ids)}}
      rescue
        e in ArgumentError -> {:halt, {:error, f, Exception.message(e)}}
      end
    end)
  end

  defp walk(%{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => g}} = node, owner, ctx) do
    target = ctx.functions[id] || get_in(ctx.models, [id, :function])
    ids = if target, do: arguments!(target["generics"], g, owner, ctx, []), else: []
    ids ++ walk(Map.values(node), owner, ctx)
  end

  defp walk(map, owner, ctx) when is_map(map), do: walk(Map.values(map), owner, ctx)
  defp walk(list, owner, ctx) when is_list(list), do: Enum.flat_map(list, &walk(&1, owner, ctx))
  defp walk(_, _, _), do: []

  defp arguments!(params, g, owner, ctx, seen) do
    clauses = params["trait_clauses"] || []

    Enum.with_index(clauses)
    |> Enum.flat_map(fn {clause, index} ->
      expected = CallModels.expand(clause["trait_"]["skip_binder"], ctx.refs)

      if is_integer(ctx.trait) and expected["id"] == ctx.trait do
        unless length(g["trait_refs"]) == length(clauses), do: reject!()
        expected = CallModels.instantiate(expected, expanded_args(g, ctx.refs))
        dictionary!(Enum.at(g["trait_refs"], index), expected, owner, ctx, seen)
      else
        []
      end
    end)
  end

  defp dictionary!(dict, expected, owner, ctx, seen) do
    with %{"kind" => kind, "trait_decl_ref" => decl} <-
           ResourceModels.dictionary(dict, ctx.traits),
         true <- CallModels.expand(decl, ctx.refs) == expected do
      case kind do
        %{"Clause" => [%{"Free" => index}, %{"regions" => []}]} ->
          clause = Enum.find(owner["generics"]["trait_clauses"], &(&1["clause_id"] == index))

          unless clause &&
                   CallModels.expand(clause["trait_"]["skip_binder"], ctx.refs) == expected,
                 do: reject!()

          []

        %{"TraitImpl" => %{"id" => id, "generics" => g}} ->
          if id in seen, do: reject!()
          impl = find(ctx.t["trait_impls"], id)

          unless impl && impl["src"] == "Normal" && impl["is_unsafe"] == false &&
                   impl["is_negative"] == false &&
                   length(g["types"]) == length(impl["generics"]["types"]) &&
                   length(g["regions"]) == length(impl["generics"]["regions"]) &&
                   g["const_generics"] == [] && impl["generics"]["const_generics"] == [] &&
                   CallModels.instantiate(
                     CallModels.expand(impl["impl_trait"], ctx.refs),
                     expanded_args(g, ctx.refs)
                   ) == expected,
                 do: reject!()

          methods = Enum.map(0..1, &method!(impl, &1, ctx))
          methods ++ arguments!(impl["generics"], g, owner, ctx, [id | seen])

        _ ->
          reject!()
      end
    else
      _ -> reject!()
    end
  end

  defp method!(impl, index, ctx) do
    with [eq, ne] <- impl["methods"],
         %{"kind" => %{"TraitMethod" => [trait, ^index]}, "skip_binder" => %{"id" => id}} <-
           Enum.at([eq, ne], index),
         true <- trait == ctx.trait,
         f when not is_nil(f) <- ctx.functions[id] || get_in(ctx.models, [id, :function]) do
      valid =
        case f["src"] do
          %{
            "TraitImpl" => %{
              "impl_ref" => %{"id" => parent},
              "item_id" => ^index,
              "reuses_default" => false
            }
          } ->
            parent == impl["def_id"]

          %{"TraitDefault" => %{"trait_ref" => %{"id" => ^trait}, "item_id" => ^index}} ->
            decl = find(ctx.t["trait_decls"], trait)
            get_in(Enum.at(decl["methods"], index), ["skip_binder", "default", "id"]) == id

          _ ->
            false
        end

      unless valid, do: reject!()
      id
    else
      _ -> reject!()
    end
  end

  defp comparison_trait(t) do
    case Enum.find(
           t["trait_decls"] || [],
           &(&1 && &1["item_meta"]["name"] == path(~w(core cmp PartialEq)))
         ) do
      %{
        "src" => "Normal",
        "is_unsafe" => false,
        "def_id" => id,
        "generics" => params,
        "methods" => [eq, ne]
      } ->
        if parameters?(params, 2, 0, false, nil) and eq["skip_binder"]["name"] == "eq" and
             ne["skip_binder"]["name"] == "ne",
           do: id

      _ ->
        nil
    end
  end

  defp parameters?(p, types, regions, clause?, trait) do
    p["const_generics"] == [] and p["trait_type_constraints"] == [] and
      Enum.map(p["types"], & &1["index"]) == Enum.to_list(0..(types - 1)//1) and
      Enum.map(p["regions"], & &1["index"]) == Enum.to_list(0..(regions - 1)//1) and
      case p["trait_clauses"] do
        [] ->
          not clause?

        [
          %{
            "clause_id" => 0,
            "trait_" => %{"regions" => [], "outlives" => [], "skip_binder" => %{"id" => ^trait}}
          }
        ] ->
          clause?

        _ ->
          false
      end
  end

  defp expanded_args(g, refs), do: Map.update!(g, "types", &CallModels.expand(&1, refs))

  defp comparison_clause?(params, trait, refs) do
    case params["trait_clauses"] do
      [clause] ->
        CallModels.expand(clause["trait_"]["skip_binder"], refs) ==
          declaration(trait, [var(0), var(1)])

      _ ->
        false
    end
  end

  defp scalar?(%{"Scalar" => %{"Integer" => %{"Unsigned" => width}}}),
    do: width in ~w(U8 U16 U32 U64 U128 Usize)

  defp scalar?(%{"Scalar" => %{"Integer" => %{"Signed" => width}}}),
    do: width in ~w(I8 I16 I32 I64 I128 Isize)

  defp scalar?(_), do: false

  defp declaration(id, types),
    do: %{
      "id" => id,
      "generics" => %{
        "regions" => [],
        "types" => types,
        "const_generics" => [],
        "trait_refs" => []
      }
    }

  defp safe?(sig),
    do: sig["is_unsafe"] == false and sig["is_variadic"] == false and sig["abi"] == "Rust"

  defp var(i), do: %{"TypeVar" => %{"Free" => i}}
  defp ref(t, i), do: %{"Ref" => [%{"Var" => %{"Free" => i}}, t, "Shared"]}
  defp slice(t), do: %{"Slice" => [t, nil]}
  defp ident(s), do: %{"Ident" => [s, 0]}
  defp path(parts), do: Enum.map(parts, &ident/1)
  defp find(rows, id), do: Enum.find(rows || [], &(&1 && &1["def_id"] == id))

  defp reject!,
    do:
      raise(
        ArgumentError,
        "missing or unsupported PartialEq implementation or captured eq/ne method"
      )
end
