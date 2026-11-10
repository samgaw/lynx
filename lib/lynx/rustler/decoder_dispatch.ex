defmodule Lynx.Rustler.DecoderDispatch do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Constants}
  alias Lynx.Rustler.DecoderModels
  @empty %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}

  # The backend already represents static trait clauses as dictionaries. Admit
  # only checked Decoder clauses and close every supplied dictionary over actual
  # first-party methods or the existing, explicitly reported primitive models.
  def audit(functions, models, translated, refs) do
    ctx = %{
      translated: translated,
      refs: refs,
      models: models,
      traits: trait_references(translated, %{}),
      functions: Map.new(Enum.reject(translated["fun_decls"], &is_nil/1), &{&1["def_id"], &1}),
      implementations: MapSet.new(functions, & &1["def_id"])
    }

    Enum.reduce_while(functions, {:ok, %{dependencies: %{}, calls: %{}}}, fn function,
                                                                             {:ok, result} ->
      try do
        {dependencies, calls} = walk(function["body"], function, ctx)

        {:cont,
         {:ok,
          %{
            dependencies:
              Map.put(result.dependencies, function["def_id"], Enum.uniq(dependencies)),
            calls: Map.put(result.calls, function["def_id"], Enum.uniq(calls))
          }}}
      rescue
        error in ArgumentError ->
          {:halt, {:error, function, Exception.message(error)}}
      end
    end)
  end

  defp walk(%{"Call" => %{"call" => %{"func" => func}}} = node, caller, ctx) do
    {ids, sites} = call(func, caller, ctx)

    Enum.reduce(Map.values(node), {ids, sites}, fn value, {ids, sites} ->
      {more, calls} = walk(value, caller, ctx)
      {ids ++ more, sites ++ calls}
    end)
  end

  defp walk(map, caller, ctx) when is_map(map), do: walk(Map.values(map), caller, ctx)

  defp walk(list, caller, ctx) when is_list(list) do
    Enum.reduce(list, {[], []}, fn value, {ids, sites} ->
      {more, calls} = walk(value, caller, ctx)
      {ids ++ more, sites ++ calls}
    end)
  end

  defp walk(_, _, _), do: {[], []}

  defp call(
         %{"Regular" => %{"kind" => %{"Trait" => [reference, 0]}, "generics" => @empty}} = raw,
         caller,
         ctx
       ) do
    ref = trait_ref!(reference, ctx)

    case ref do
      %{
        "kind" => %{"Clause" => [%{"Free" => index}, %{"regions" => []}]},
        "trait_decl_ref" => actual
      } ->
        expected = clause!(caller, index, ctx)
        require!(same_trait?(actual, expected, ctx))
        {[], [raw]}

      _ ->
        reject!()
    end
  end

  defp call(%{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => args}}, caller, ctx) do
    target = ctx.functions[id]
    clauses = if target, do: target["generics"]["trait_clauses"], else: []

    if Enum.any?(clauses, &decoder_clause?(&1, ctx)) do
      params = target["generics"]
      require!(params["const_generics"] == [] and params["trait_type_constraints"] == [])

      require!(
        length(args["types"]) == length(params["types"]) and
          length(args["regions"]) == length(params["regions"]) and
          length(args["trait_refs"]) == length(clauses) and args["const_generics"] == []
      )

      ids =
        for {_clause, index} <- Enum.with_index(clauses), reduce: [] do
          ids ->
            expected = clause!(target, index, ctx) |> instantiate(args, ctx)
            ids ++ dictionary!(Enum.at(args["trait_refs"], index), expected, caller, ctx)
        end

      {ids, []}
    else
      {[], []}
    end
  end

  defp call(_, _, _), do: {[], []}

  defp dictionary!(reference, expected, caller, ctx) do
    ref = trait_ref!(reference, ctx)
    require!(same_trait?(ref["trait_decl_ref"], expected, ctx))

    case ref["kind"] do
      %{"Clause" => [%{"Free" => index}, %{"regions" => []}]} ->
        require!(same_trait?(clause!(caller, index, ctx), expected, ctx))
        []

      %{"TraitImpl" => %{"id" => id, "generics" => args}} ->
        impl = find!(ctx.translated["trait_impls"], id)
        params = impl["generics"]

        require!(
          params["types"] == [] and params["const_generics"] == [] and
            params["trait_clauses"] == [] and params["trait_type_constraints"] == [] and
            params["outlives"] == []
        )

        require!(
          length(args["regions"]) == length(params["regions"]) and
            Constants.empty_arguments?(%{args | "regions" => []})
        )

        require!(same_trait?(instantiate(impl["impl_trait"], args, ctx), expected, ctx))

        method =
          case impl["methods"] do
            [%{"skip_binder" => %{"id" => id}}] -> id
            _ -> reject!()
          end

        function = Map.get(ctx.functions, method) || reject!()
        [self] = expected["generics"]["types"]
        self = CallModels.expand(self, ctx.refs)
        require!(DecoderModels.decoder_method?(function, self, ctx.translated, ctx.refs))

        require!(
          (MapSet.member?(ctx.implementations, method) and is_map(function["body"])) or
            get_in(ctx.models, [method, :decoder_trait]) == expected["id"]
        )

        [method]

      _ ->
        reject!()
    end
  end

  defp clause!(function, index, ctx) do
    clause = Enum.at(function["generics"]["trait_clauses"], index)
    require!(is_map(clause) and clause["clause_id"] == index and decoder_clause?(clause, ctx))
    %{"regions" => [], "outlives" => [], "skip_binder" => trait} = clause["trait_"]
    CallModels.expand(trait, ctx.refs)
  end

  defp decoder_clause?(
         %{
           "trait_" => %{
             "regions" => [],
             "outlives" => [],
             "skip_binder" => %{"id" => id, "generics" => args}
           }
         },
         ctx
       ) do
    DecoderModels.decoder_trait?(id, ctx.translated, ctx.refs) and
      length(args["types"]) == 1 and length(args["regions"]) == 1 and
      args["const_generics"] == [] and args["trait_refs"] == []
  end

  defp decoder_clause?(_, _), do: false

  defp same_trait?(left, right, ctx) do
    left = CallModels.expand(left, ctx.refs)
    right = CallModels.expand(right, ctx.refs)

    with %{"id" => id, "generics" => a} <- left,
         %{"id" => ^id, "generics" => b} <- right do
      DecoderModels.decoder_trait?(id, ctx.translated, ctx.refs) and
        length(a["regions"]) == 1 and length(b["regions"]) == 1 and
        Enum.all?(a["regions"] ++ b["regions"], &region?/1) and
        %{a | "regions" => []} == %{b | "regions" => []}
    else
      _ -> false
    end
  end

  # Lifetime names disappear in the backend's dictionary representation. Compare
  # the actual trait/Self identities and require valid compiler lifetime forms;
  # do not rewrite any executable body or erase a borrow operation.
  defp region?(r) when r in ["Static", "Erased"], do: true
  defp region?(%{"Body" => n}), do: is_integer(n) and n >= 0
  defp region?(%{"Var" => %{"Free" => n}}), do: is_integer(n) and n >= 0
  defp region?(_), do: false

  defp trait_ref!(%{"regions" => [], "outlives" => [], "skip_binder" => ref}, ctx),
    do: trait_ref!(ref, ctx)

  defp trait_ref!(%{"Value" => [_, %{"kind" => _, "trait_decl_ref" => _} = ref]}, _), do: ref
  defp trait_ref!(%{"Deduplicated" => id}, ctx), do: Map.get(ctx.traits, id) || reject!()
  defp trait_ref!(%{"kind" => _, "trait_decl_ref" => _} = ref, _), do: ref
  defp trait_ref!(_, _), do: reject!()

  defp trait_references(%{"Value" => [id, %{"kind" => _, "trait_decl_ref" => _} = ref]}, acc) do
    require!(not Map.has_key?(acc, id) or acc[id] == ref)
    trait_references(ref, Map.put(acc, id, ref))
  end

  defp trait_references(map, acc) when is_map(map), do: trait_references(Map.values(map), acc)

  defp trait_references(list, acc) when is_list(list),
    do: Enum.reduce(list, acc, &trait_references/2)

  defp trait_references(_, acc), do: acc

  defp instantiate(value, args, ctx), do: value |> CallModels.expand(ctx.refs) |> substitute(args)
  defp substitute(%{"TypeVar" => %{"Free" => index}}, args), do: Enum.fetch!(args["types"], index)
  defp substitute(%{"Var" => %{"Free" => index}}, args), do: Enum.fetch!(args["regions"], index)

  defp substitute(map, args) when is_map(map),
    do: Map.new(map, fn {k, v} -> {k, substitute(v, args)} end)

  defp substitute(list, args) when is_list(list), do: Enum.map(list, &substitute(&1, args))
  defp substitute(value, _), do: value
  defp find!(items, id), do: Enum.find(items, &(&1 && &1["def_id"] == id)) || reject!()
  defp require!(true), do: :ok
  defp require!(_), do: reject!()

  defp reject!,
    do:
      raise(ArgumentError, "missing or inconsistent static Rustler Decoder dictionary dependency")
end
