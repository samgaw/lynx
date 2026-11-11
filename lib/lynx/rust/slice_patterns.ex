defmodule Lynx.Rust.SlicePatterns do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, LLBCJson, ResourceModels}

  # Retain upstream implementations, including pattern conversion and comparison
  # order. No recognition or conversion body is supplied by this module.
  def selected?(f, t) do
    refs = LLBC.type_references!(t)
    trait = pattern_trait(t, refs)

    is_integer(trait) and safe?(f) and
      (strip?(f, t, refs, trait) or standard_method?(f, t, refs, trait))
  end

  defp strip?(f, t, refs, trait) do
    p = f["generics"]

    eq =
      Enum.find(
        t["trait_decls"] || [],
        &(&1 && &1["item_meta"]["name"] == path(~w(core cmp PartialEq)))
      )

    option =
      Enum.find(
        t["type_decls"] || [],
        &(&1 && &1["item_meta"]["name"] == path(~w(core option Option)))
      )

    with "Normal" <- f["src"],
         [
           _,
           _,
           %{"Impl" => %{"Ty" => %{"params" => parent_params, "skip_binder" => parent}}},
           %{"Ident" => [method, 0]}
         ] <- f["item_meta"]["name"],
         true <- method in ["strip_prefix", "strip_suffix"],
         true <- params?(parent_params, 1, 0, 0, []),
         true <- expand(parent, refs) == slice(%{"TypeVar" => %{"Bound" => [0, 0]}}),
         true <- params?(p, 2, 2, 0, [0, 1]),
         [pattern, equality] <- p["trait_clauses"],
         true <- clause(pattern, refs) == decl(trait, [var(1), var(0)]),
         true <- eq != nil and clause(equality, refs) == decl(eq["def_id"], [var(0), var(0)]),
         true <- expand(f["signature"]["inputs"], refs) == [ref(slice(var(0)), 0), ref(var(1), 1)],
         true <- option != nil do
      expand(f["signature"]["output"], refs) == %{
        "Adt" => %{
          "id" => option["def_id"],
          "builtin" => nil,
          "generics" => args([ref(slice(var(0)), 0)])
        }
      }
    else
      _ -> false
    end
  end

  defp standard_method?(f, t, refs, trait) do
    with %{
           "TraitImpl" => %{
             "impl_ref" => %{"id" => impl_id},
             "trait_ref" => %{"id" => ^trait},
             "item_id" => 0,
             "reuses_default" => false
           }
         } <- f["src"],
         true <-
           f["item_meta"]["name"] ==
             path(~w(core slice)) ++ [%{"Impl" => %{"Trait" => impl_id}}, ident("as_slice")],
         %{
           "src" => "Normal",
           "is_unsafe" => false,
           "is_negative" => false,
           "impl_trait" => %{"id" => ^trait, "generics" => implemented}
         } = impl <- find(t["trait_impls"], impl_id),
         [self, item] <- expand(implemented["types"], refs),
         true <- item == var(0),
         constants when constants in [0, 1] <- container(self),
         true <- params?(impl["generics"], 1, 0, constants, []),
         true <- params?(f["generics"], 1, 1, constants, []),
         true <-
           expand(Enum.map(f["generics"]["const_generics"], & &1["ty"]), refs) ==
             List.duplicate(usize(), constants),
         true <-
           expand(Enum.map(impl["generics"]["const_generics"], & &1["ty"]), refs) ==
             List.duplicate(usize(), constants),
         true <- expand(f["signature"]["inputs"], refs) == [ref(self, 0)],
         true <- expand(f["signature"]["output"], refs) == ref(slice(item), 0),
         [%{"kind" => %{"TraitMethod" => [^trait, 0]}, "skip_binder" => %{"id" => id}}] <-
           impl["methods"] do
      id == f["def_id"] and
        expand(f["src"]["TraitImpl"]["trait_ref"], refs) == expand(impl["impl_trait"], refs)
    else
      _ -> false
    end
  end

  defp container(%{"Slice" => [%{"TypeVar" => %{"Free" => 0}}, nil]}), do: 0

  defp container(%{
         "Array" => [
           %{"TypeVar" => %{"Free" => 0}},
           [%{"Var" => %{"Free" => 0}}, %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}],
           nil
         ]
       }),
       do: 1

  defp container(_), do: nil

  def audit(functions, t, refs) do
    # Constants, types and dictionaries have separate hash-cons families.
    # Hydrate constants before instantiating array patterns, without decoding a
    # constant reference through the type table or treating it as a lifetime.
    t = LLBCJson.restore_constant_references!(t, t)

    ctx = %{
      t: t,
      refs: refs,
      trait: pattern_trait(t, refs),
      traits: ResourceModels.trait_references(t),
      functions:
        functions
        |> LLBCJson.restore_constant_references!(t)
        |> Map.new(fn f -> {f["def_id"], f} end)
    }

    Enum.reduce_while(functions, {:ok, %{dependencies: %{}, calls: %{}}}, fn f, {:ok, result} ->
      try do
        owner = ctx.functions[f["def_id"]]
        {ids, calls} = walk(owner["body"], owner, ctx)

        {:cont,
         {:ok,
          %{
            dependencies: Map.put(result.dependencies, f["def_id"], Enum.uniq(ids)),
            calls: Map.put(result.calls, f["def_id"], Enum.uniq(calls))
          }}}
      rescue
        error in ArgumentError -> {:halt, {:error, f, Exception.message(error)}}
      end
    end)
  end

  defp walk(%{"Call" => %{"call" => %{"func" => func}}} = node, owner, ctx) do
    {ids, calls} = call(func, owner, ctx)
    {more, nested} = walk(Map.values(node), owner, ctx)
    {ids ++ more, calls ++ nested}
  end

  defp walk(map, owner, ctx) when is_map(map), do: walk(Map.values(map), owner, ctx)

  defp walk(list, owner, ctx) when is_list(list) do
    Enum.reduce(list, {[], []}, fn node, {ids, calls} ->
      {more, nested} = walk(node, owner, ctx)
      {ids ++ more, calls ++ nested}
    end)
  end

  defp walk(_, _, _), do: {[], []}

  defp call(%{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => g}}, owner, ctx) do
    case ctx.functions[id] do
      nil -> {[], []}
      target -> {arguments!(target["generics"], g, owner, ctx), []}
    end
  end

  defp call(
         %{"Regular" => %{"kind" => %{"Trait" => [raw, 0]}, "generics" => g}} = func,
         owner,
         ctx
       ) do
    value =
      ResourceModels.dictionary(
        %{"regions" => [], "outlives" => [], "skip_binder" => raw},
        ctx.traits
      )

    if (is_integer(ctx.trait) and value) && value["trait_decl_ref"]["id"] == ctx.trait do
      unless length(g["regions"]) == 1 and g["types"] == [] and g["const_generics"] == [] and
               g["trait_refs"] == [],
             do: reject!()

      ids = dictionary!(value, expand(value["trait_decl_ref"], ctx.refs), owner, ctx)
      {ids, [func]}
    else
      {[], []}
    end
  end

  defp call(_, _, _), do: {[], []}

  defp arguments!(params, g, owner, ctx) do
    Enum.flat_map(Enum.with_index(params["trait_clauses"] || []), fn {bound, index} ->
      expected = clause(bound, ctx.refs)

      if is_integer(ctx.trait) and expected["id"] == ctx.trait do
        unless length(g["trait_refs"]) == length(params["trait_clauses"]), do: reject!()
        expected = substitute(expected, expanded_args(g, ctx.refs))

        dictionary!(
          ResourceModels.dictionary(Enum.at(g["trait_refs"], index), ctx.traits),
          expected,
          owner,
          ctx
        )
      else
        []
      end
    end)
  end

  defp dictionary!(%{"trait_decl_ref" => actual, "kind" => kind}, expected, owner, ctx) do
    unless expand(actual, ctx.refs) == expected, do: reject!()

    case kind do
      %{"Clause" => [%{"Free" => index}, %{"regions" => []}]} ->
        bound = Enum.find(owner["generics"]["trait_clauses"], &(&1["clause_id"] == index))
        unless bound && clause(bound, ctx.refs) == expected, do: reject!()
        []

      %{"TraitImpl" => %{"id" => id, "generics" => g}} ->
        impl = find(ctx.t["trait_impls"], id)

        unless impl && impl["src"] == "Normal" && impl["is_unsafe"] == false &&
                 impl["is_negative"] == false &&
                 g["trait_refs"] == [] && impl["generics"]["trait_clauses"] == [] &&
                 impl["generics"]["trait_type_constraints"] == [] &&
                 impl["types"] == [nil] && impl["consts"] == [] &&
                 length(g["types"]) == length(impl["generics"]["types"]) &&
                 length(g["regions"]) == length(impl["generics"]["regions"]) &&
                 length(g["const_generics"]) == length(impl["generics"]["const_generics"]),
               do: reject!()

        implemented = expand(impl["impl_trait"], ctx.refs)

        if g["const_generics"] != [] do
          method = get_in(List.first(impl["methods"] || []), ["skip_binder", "id"])

          unless standard_method?(ctx.functions[method], ctx.t, ctx.refs, ctx.trait),
            do:
              raise(
                ArgumentError,
                "unsupported constant-generic first-party SlicePattern implementation"
              )
        end

        unless substitute(implemented, expanded_args(g, ctx.refs)) == expected,
          do: reject!()

        with [%{"kind" => %{"TraitMethod" => [trait, 0]}, "skip_binder" => %{"id" => method}}] <-
               impl["methods"],
             true <- trait == ctx.trait,
             %{
               "src" => %{
                 "TraitImpl" => %{
                   "impl_ref" => %{"id" => ^id},
                   "item_id" => 0,
                   "reuses_default" => false
                 }
               }
             } = f <- ctx.functions[method],
             true <- safe?(f) and match?(%{"Structured" => _}, f["body"]) do
          unless expand(f["src"]["TraitImpl"]["trait_ref"], ctx.refs) == implemented,
            do: reject!()

          [method]
        else
          _ -> reject!()
        end

      _ ->
        reject!()
    end
  end

  defp dictionary!(_, _, _, _), do: reject!()

  defp substitute(%{"Array" => [type, [%{"Var" => %{"Free" => index}}, _], proof]}, g),
    do: %{"Array" => [substitute(type, g), Enum.fetch!(g["const_generics"], index), proof]}

  defp substitute(%{"TypeVar" => %{"Free" => index}}, g), do: Enum.fetch!(g["types"], index)
  defp substitute(%{"Var" => %{"Free" => index}}, g), do: Enum.fetch!(g["regions"], index)

  defp substitute(map, g) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, substitute(v, g)} end)

  defp substitute(list, g) when is_list(list), do: Enum.map(list, &substitute(&1, g))
  defp substitute(value, _), do: value

  defp expanded_args(g, refs),
    do:
      g
      |> Map.update!("types", &expand(&1, refs))
      |> Map.update!("const_generics", &expand(&1, refs))

  defp pattern_trait(t, refs) do
    case Enum.find(
           t["trait_decls"] || [],
           &(&1 && &1["item_meta"]["name"] == path(~w(core slice SlicePattern)))
         ) do
      %{
        "src" => "Normal",
        "is_unsafe" => false,
        "def_id" => id,
        "generics" => p,
        "methods" => [
          %{
            "kind" => %{"TraitMethod" => [id, 0]},
            "params" => method_params,
            "skip_binder" => %{"name" => "as_slice", "signature" => sig, "default" => nil}
          }
        ]
      } = trait ->
        expected = %{
          "inputs" => [%{"Ref" => [%{"Var" => %{"Bound" => [0, 0]}}, var(0), "Shared"]}],
          "output" => %{"Ref" => [%{"Var" => %{"Bound" => [0, 0]}}, slice(var(1)), "Shared"]},
          "abi" => "Rust",
          "is_unsafe" => false,
          "is_variadic" => false
        }

        if params?(p, 2, 0, 0, []) and params?(method_params, 0, 1, 0, []) and
             expand(sig, refs) == expected and
             trait["types"] == [nil] and trait["consts"] == [] and
             trait["implied_clauses"] == [],
           do: id

      _ ->
        nil
    end
  end

  defp params?(p, types, regions, constants, clauses) do
    Enum.map(p["types"], & &1["index"]) == indices(types) and
      Enum.map(p["regions"], & &1["index"]) == indices(regions) and
      Enum.map(p["const_generics"], & &1["index"]) == indices(constants) and
      p["trait_type_constraints"] == [] and
      Enum.map(p["trait_clauses"], & &1["clause_id"]) == clauses
  end

  defp safe?(f),
    do:
      f["signature"]["abi"] == "Rust" and f["signature"]["is_unsafe"] == false and
        f["signature"]["is_variadic"] == false

  defp indices(0), do: []
  defp indices(n), do: Enum.to_list(0..(n - 1))
  defp clause(c, refs), do: expand(c["trait_"]["skip_binder"], refs)
  defp decl(id, types), do: %{"id" => id, "generics" => args(types)}

  defp args(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp var(i), do: %{"TypeVar" => %{"Free" => i}}
  defp usize, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
  defp ref(t, i), do: %{"Ref" => [%{"Var" => %{"Free" => i}}, t, "Shared"]}
  defp slice(t), do: %{"Slice" => [t, nil]}
  defp ident(s), do: %{"Ident" => [s, 0]}
  defp path(s), do: Enum.map(s, &ident/1)
  defp expand(v, refs), do: CallModels.expand(v, refs)
  defp find(rows, id), do: Enum.find(rows || [], &(&1 && &1["def_id"] == id))

  defp reject!,
    do:
      raise(
        ArgumentError,
        "missing or inconsistent SlicePattern implementation, associated item or as_slice method"
      )
end
