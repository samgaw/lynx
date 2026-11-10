defmodule Lynx.Rust.OwnershipDispatch do
  @moduledoc false
  alias Lynx.Rust.{CallModels, DropModels, ResourceModels}
  @empty %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}

  # Retained ownership dictionaries are executable dependencies. A generic
  # clause is a parameter, not an assumed implementation; callers must supply
  # matching clauses or actual instances whose methods are also audited bodies.
  def audit!(functions, translated, refs, primitives) do
    ctx = %{
      functions: Map.new(functions, &{&1["def_id"], &1}),
      translated: translated,
      refs: refs,
      traits: ResourceModels.trait_references(translated),
      primitives: MapSet.new(primitives, & &1.function_id)
    }

    unsafe =
      for function <- functions,
          function["signature"]["is_unsafe"] == true do
        id = function["def_id"]

        unless MapSet.member?(ctx.primitives, id) or generated_method?(function, ctx),
          do: reject!("unsupported unsafe ownership implementation #{id}")

        id
      end

    rows =
      for function <- functions do
        try do
          {dependencies, calls} = walk(function["body"], function, ctx)
          {function["def_id"], {Enum.uniq(dependencies), Enum.uniq(calls)}}
        rescue
          error in ArgumentError ->
            raise ArgumentError,
                  "#{Exception.message(error)} in function #{function["def_id"]}: " <>
                    inspect(function["item_meta"]["name"])
        end
      end

    %{
      unsafe: MapSet.new(unsafe),
      dependencies: Map.new(rows, fn {id, {deps, _}} -> {id, deps} end),
      calls: Map.new(rows, fn {id, {_, calls}} -> {id, calls} end)
    }
  end

  defp walk(%{"Call" => %{"call" => %{"func" => func}}} = node, caller, ctx) do
    {ids, calls} = call(func, caller, ctx)
    {more, nested} = walk(Map.values(node), caller, ctx)
    {ids ++ more, calls ++ nested}
  end

  defp walk(map, caller, ctx) when is_map(map), do: walk(Map.values(map), caller, ctx)

  defp walk(list, caller, ctx) when is_list(list) do
    Enum.reduce(list, {[], []}, fn item, {ids, calls} ->
      {more, nested} = walk(item, caller, ctx)
      {ids ++ more, calls ++ nested}
    end)
  end

  defp walk(_, _, _), do: {[], []}

  defp call(
         %{"Regular" => %{"kind" => %{"Trait" => [raw, 0]}, "generics" => args}} = func,
         caller,
         ctx
       ) do
    ref = reference!(raw, ctx)

    if ownership?(ref["trait_decl_ref"], ctx) do
      require!(length(args["regions"]) == 1 and %{args | "regions" => []} == @empty)
      {dictionary!(ref, ref["trait_decl_ref"], caller, ctx, []), [func]}
    else
      {[], []}
    end
  end

  defp call(%{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => args}}, caller, ctx) do
    target = ctx.functions[id]
    clauses = if target, do: target["generics"]["trait_clauses"], else: []

    if Enum.any?(clauses, &ownership_clause?(&1, ctx)) do
      params = target["generics"]
      arguments!(args, params)

      ids =
        for {clause, index} <- Enum.with_index(clauses),
            ownership_clause?(clause, ctx),
            reduce: [] do
          ids ->
            expected = instantiate(clause!(target, index, ctx), args, ctx)
            ids ++ dictionary!(Enum.at(args["trait_refs"], index), expected, caller, ctx, [])
        end

      {ids, []}
    else
      {[], []}
    end
  end

  defp call(_, _, _), do: {[], []}

  defp dictionary!(raw, expected, caller, ctx, seen) do
    ref = reference!(raw, ctx)
    require!(same?(ref["trait_decl_ref"], expected, ctx))

    case ref["kind"] do
      %{"Clause" => [%{"Free" => index}, %{"regions" => []}]} ->
        require!(same?(clause!(caller, index, ctx), expected, ctx))
        []

      %{"TraitImpl" => %{"id" => id, "generics" => args}} ->
        require!(id not in seen)
        impl = find!(ctx.translated["trait_impls"], id)
        arguments!(args, impl["generics"])
        require!(same?(instantiate(impl["impl_trait"], args, ctx), expected, ctx))
        require!(impl["is_negative"] == false and impl["is_unsafe"] == false)
        require!(impl["consts"] == [] and impl["types"] == [])

        {trait, method} =
          case impl["methods"] do
            [%{"kind" => %{"TraitMethod" => [trait, 0]}, "skip_binder" => method}] ->
              {trait, method}

            _ ->
              reject!("missing or ambiguous destructor method")
          end

        require!(trait == expected["id"])
        function = ctx.functions[method["id"]] || reject!("missing destructor method body")
        require!(is_map(function["body"]) and function["item_meta"]["opacity"] == "Transparent")

        require!(
          MapSet.member?(ctx.primitives, method["id"]) or method_source?(function, id, impl, ctx)
        )

        dependencies =
          for {_, index} <- Enum.with_index(impl["generics"]["trait_clauses"]), reduce: [] do
            ids ->
              clause = clause_from!(impl, index, ctx) |> then(&instantiate(&1, args, ctx))

              ids ++
                dictionary!(Enum.at(args["trait_refs"], index), clause, caller, ctx, [id | seen])
          end

        [method["id"] | dependencies]

      _ ->
        reject!("untracked or unsupported destructor dictionary")
    end
  end

  defp generated_method?(function, ctx) do
    with true <- DropModels.generated?(function),
         %{"TraitImpl" => %{"impl_ref" => %{"id" => id}}} <- function["src"],
         impl when is_map(impl) <-
           Enum.find(ctx.translated["trait_impls"], &(&1 && &1["def_id"] == id)),
         true <- impl["src"] == "Destruct",
         trait <-
           Enum.find(
             ctx.translated["trait_decls"],
             &(&1 && &1["def_id"] == impl["impl_trait"]["id"])
           ),
         true <- is_map(trait) and trait["item_meta"]["name"] == path("Destruct"),
         true <- method_source?(function, id, impl, ctx) do
      true
    else
      _ -> false
    end
  end

  defp method_source?(function, id, impl, ctx) do
    with %{
           "TraitImpl" => %{
             "impl_ref" => %{"id" => ^id},
             "trait_ref" => trait,
             "item_id" => 0,
             "reuses_default" => false
           }
         } <- function["src"],
         true <- same?(trait, impl["impl_trait"], ctx),
         [%{"skip_binder" => %{"id" => method}}] <- impl["methods"],
         true <- method == function["def_id"],
         %{"inputs" => [input], "output" => output, "is_variadic" => false, "abi" => "Rust"} <-
           function["signature"],
         %{"Ref" => [_, self, "Mut"]} <- CallModels.expand(input, ctx.refs),
         [expected] <- CallModels.expand(trait["generics"]["types"], ctx.refs),
         true <- self == expected,
         %{"Adt" => %{"builtin" => "Tuple", "generics" => @empty}} <-
           CallModels.expand(output, ctx.refs) do
      true
    else
      _ -> false
    end
  end

  defp clause!(function, index, ctx), do: clause_from!(function, index, ctx)

  defp clause_from!(item, index, ctx) do
    clause = Enum.at(item["generics"]["trait_clauses"], index)
    require!(is_map(clause) and clause["clause_id"] == index and ownership_clause?(clause, ctx))
    clause["trait_"]["skip_binder"] |> CallModels.expand(ctx.refs)
  end

  defp ownership_clause?(
         %{"trait_" => %{"regions" => [], "outlives" => [], "skip_binder" => trait}},
         ctx
       ),
       do: ownership?(trait, ctx)

  defp ownership_clause?(_, _), do: false

  defp ownership?(%{"id" => id, "generics" => args}, ctx) do
    trait = Enum.find(ctx.translated["trait_decls"], &(&1 && &1["def_id"] == id))

    is_map(trait) and trait["item_meta"]["name"] in [path("Destruct"), path("Drop")] and
      length(args["types"]) == 1 and %{args | "types" => []} == @empty
  end

  defp ownership?(_, _), do: false
  defp path(name), do: [%{"Ident" => ["LynxCompilerOwnership", 0]}, %{"Ident" => [name, 0]}]

  defp same?(left, right, ctx),
    do:
      ownership?(left, ctx) and ownership?(right, ctx) and
        CallModels.expand(left, ctx.refs) == CallModels.expand(right, ctx.refs)

  defp arguments!(args, params) do
    require!(params["const_generics"] == [] and params["trait_type_constraints"] == [])

    require!(
      length(args["regions"]) == length(params["regions"]) and
        length(args["types"]) == length(params["types"]) and args["const_generics"] == [] and
        length(args["trait_refs"]) == length(params["trait_clauses"])
    )
  end

  defp reference!(%{"regions" => [], "outlives" => [], "skip_binder" => ref}, ctx),
    do: reference!(ref, ctx)

  defp reference!(%{"Value" => [_, ref]}, _), do: ref

  defp reference!(%{"Deduplicated" => id}, ctx),
    do: ctx.traits[id] || reject!("missing dictionary identity")

  defp reference!(%{"kind" => _, "trait_decl_ref" => _} = ref, _), do: ref
  defp reference!(_, _), do: reject!("invalid dictionary")

  defp instantiate(value, args, ctx), do: value |> CallModels.expand(ctx.refs) |> substitute(args)
  defp substitute(%{"TypeVar" => %{"Free" => index}}, args), do: Enum.fetch!(args["types"], index)
  defp substitute(%{"Var" => %{"Free" => index}}, args), do: Enum.fetch!(args["regions"], index)

  defp substitute(map, args) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, substitute(v, args)} end)

  defp substitute(list, args) when is_list(list), do: Enum.map(list, &substitute(&1, args))
  defp substitute(value, _), do: value

  defp find!(items, id),
    do: Enum.find(items, &(&1 && &1["def_id"] == id)) || reject!("missing instance")

  defp require!(true), do: :ok
  defp require!(_), do: reject!("inconsistent ownership implementation")
  defp reject!(message), do: raise(ArgumentError, "explicit Rust ownership: " <> message)
end
