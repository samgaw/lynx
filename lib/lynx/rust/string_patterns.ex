defmodule Lynx.Rust.StringPatterns do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, LLBCJson, ResourceModels, StringModels}
  @path ~w(core str pattern Pattern)
  @slot 2

  def includes, do: ["core::str::_::starts_with", "core::str::pattern::_::is_prefix_of"]

  def selected?(f, t) do
    refs = LLBC.type_references!(t)
    trait = trait(t, refs)
    is_integer(trait) and safe?(f) and (starts?(f, t, refs, trait) or method?(f, t, refs, trait))
  end

  defp starts?(f, t, refs, trait) do
    with true <- expand(f["signature"]["output"], refs) == %{"Scalar" => "Bool"},
         "Normal" <- f["src"],
         [
           %{"Ident" => ["core", 0]},
           %{"Ident" => ["str", 0]},
           %{
             "Impl" => %{
               "Ty" => %{
                 "kind" => "InherentImplBlock",
                 "params" => parent_params,
                 "skip_binder" => parent
               }
             }
           },
           %{"Ident" => ["starts_with", 0]}
         ] <- f["item_meta"]["name"],
         true <- params?(parent_params, 0, 0, 0),
         true <- params?(f["generics"], 1, 1, 1),
         [bound] <- f["generics"]["trait_clauses"],
         true <- clause(bound, refs) == decl(trait, var()),
         str = expand(parent, refs),
         true <- StringModels.borrowed_type?(ref(str, region(0)), t, refs) do
      expand(f["signature"]["inputs"], refs) == [ref(str, region(0)), var()]
    else
      _ -> false
    end
  end

  defp method?(f, t, refs, trait) do
    with true <- expand(f["signature"]["output"], refs) == %{"Scalar" => "Bool"},
         %{
           "TraitImpl" => %{
             "impl_ref" => %{"id" => id},
             "trait_ref" => %{"id" => ^trait},
             "item_id" => @slot,
             "reuses_default" => false
           }
         } <- f["src"],
         true <-
           f["item_meta"]["name"] ==
             path(~w(core str pattern)) ++ [%{"Impl" => %{"Trait" => id}}, ident("is_prefix_of")],
         true <- params?(f["generics"], 0, 2, 0),
         [prefix, text] <- expand(f["signature"]["inputs"], refs),
         %{"Ref" => [r, str, "Shared"]} <- prefix,
         true <- r == region(0) and text == ref(str, region(1)),
         true <- StringModels.borrowed_type?(prefix, t, refs),
         impl when is_map(impl) <- find(t["trait_impls"], id),
         true <-
           impl["src"] == "Normal" and impl["is_unsafe"] == false and impl["is_negative"] == false,
         true <- params?(impl["generics"], 0, 1, 0),
         true <-
           impl["item_meta"]["name"] ==
             path(~w(core str pattern)) ++ [%{"Impl" => %{"Trait" => id}}],
         true <- impl["consts"] == [] and impl["implied_trait_refs"] == [],
         true <- expand(impl["impl_trait"], refs) == decl(trait, prefix),
         true <- expand(f["src"]["TraitImpl"]["trait_ref"], refs) == decl(trait, prefix),
         true <-
           expand(f["src"]["TraitImpl"]["impl_ref"]["generics"], refs) == args([], [region(0)]),
         %{
           "kind" => %{"TraitMethod" => [^trait, @slot]},
           "params" => p,
           "skip_binder" => %{"id" => method_id, "generics" => g}
         } <- Enum.at(impl["methods"], @slot) do
      method_id == f["def_id"] and params?(p, 0, 1, 0) and
        expand(g, refs) == args([], [region(0), %{"Var" => %{"Bound" => [0, 0]}}])
    else
      _ -> false
    end
  end

  def audit(functions, t, refs) do
    ctx = %{
      t: t,
      refs: refs,
      trait: trait(t, refs),
      traits: ResourceModels.trait_references(t),
      functions: Map.new(functions, &{&1["def_id"], &1})
    }

    Enum.reduce_while(functions, {:ok, %{dependencies: %{}, calls: %{}}}, fn f, {:ok, result} ->
      try do
        {ids, calls} = walk(f["body"], f, ctx)

        {:cont,
         {:ok,
          %{
            dependencies: Map.put(result.dependencies, f["def_id"], Enum.uniq(ids)),
            calls: Map.put(result.calls, f["def_id"], Enum.uniq(calls))
          }}}
      rescue
        e in ArgumentError -> {:halt, {:error, f, Exception.message(e)}}
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
    target = ctx.functions[id]
    ids = if target, do: arguments!(target["generics"], g, owner, ctx), else: []
    {ids, []}
  end

  defp call(
         %{"Regular" => %{"kind" => %{"Trait" => [raw, slot]}, "generics" => g}} = func,
         owner,
         ctx
       ) do
    value =
      ResourceModels.dictionary(
        %{"regions" => [], "outlives" => [], "skip_binder" => raw},
        ctx.traits
      )

    if (is_integer(ctx.trait) and value) && value["trait_decl_ref"]["id"] == ctx.trait do
      unless slot == @slot and starts?(owner, ctx.t, ctx.refs, ctx.trait) and
               length(g["regions"]) == 1 and g["types"] == [] and g["trait_refs"] == [] and
               g["const_generics"] == [],
             do: reject!()

      {dictionary!(value, expand(value["trait_decl_ref"], ctx.refs), owner, ctx), [func]}
    else
      {[], []}
    end
  end

  defp call(_, _, _), do: {[], []}

  defp arguments!(params, g, owner, ctx) do
    for {bound, index} <- Enum.with_index(params["trait_clauses"] || []),
        expected = clause(bound, ctx.refs),
        is_integer(ctx.trait) and expected["id"] == ctx.trait,
        reduce: [] do
      ids ->
        unless length(g["trait_refs"]) == length(params["trait_clauses"]), do: reject!()

        expected =
          CallModels.instantiate(expected, Map.update!(g, "types", &expand(&1, ctx.refs)))

        ids ++
          dictionary!(
            ResourceModels.dictionary(Enum.at(g["trait_refs"], index), ctx.traits),
            expected,
            owner,
            ctx
          )
    end
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
        method = if impl, do: get_in(Enum.at(impl["methods"], @slot), ["skip_binder", "id"])
        f = ctx.functions[method]

        unless f && safe?(f) && method?(f, ctx.t, ctx.refs, ctx.trait) &&
                 length(g["regions"]) == 1 && g["types"] == [] && g["const_generics"] == [] &&
                 g["trait_refs"] == [] &&
                 CallModels.instantiate(expand(impl["impl_trait"], ctx.refs), g) == expected,
               do: reject!()

        [method]

      _ ->
        reject!()
    end
  end

  defp dictionary!(_, _, _, _), do: reject!()

  # Only the unused foreign searcher interface is projected away. Executable
  # prefix bodies and function identities are retained; the full input is audited
  # before this backend view is produced.
  def project!(document, audit) do
    t = document["translated"]
    refs = LLBC.type_references!(document)
    id = trait(t, refs)

    if is_integer(id) and Enum.any?(audit.functions, &starts?(&1, t, refs, id)) do
      document =
        document
        |> LLBCJson.restore_type_references!(document)
        |> LLBCJson.restore_trait_references!(document)
        |> LLBCJson.restore_constant_references!(document)
        |> LLBCJson.restore_spans!(document)

      t = document["translated"]
      kept = MapSet.new(audit.functions, & &1["def_id"])

      original_functions =
        Enum.filter(t["fun_decls"], &(&1 && MapSet.member?(kept, &1["def_id"])))

      if Enum.any?(original_functions, &searcher?(Map.take(&1, ~w(signature body)), id)),
        do:
          raise(
            ArgumentError,
            "string prefix extraction cannot project an observed associated searcher type"
          )

      functions =
        Enum.map(t["fun_decls"], fn f ->
          source = if f && is_map(f["src"]), do: f["src"]["TraitImpl"] || f["src"]["TraitDefault"]

          if source && source["trait_ref"]["id"] == id && !MapSet.member?(kept, f["def_id"]),
            do: nil,
            else: f
        end)

      traits =
        Enum.map(t["trait_decls"], fn d ->
          if d && d["def_id"] == id do
            method = Enum.at(d["methods"], @slot) |> put_in(["skip_binder", "default"], nil)
            %{d | "types" => [], "methods" => [method]}
          else
            d
          end
        end)

      impls =
        Enum.map(t["trait_impls"], fn d ->
          if d && d["impl_trait"]["id"] == id,
            do: %{d | "types" => [], "methods" => [Enum.at(d["methods"], @slot)]},
            else: d
        end)

      document =
        put_in(document, ["translated"], %{
          t
          | "fun_decls" => functions,
            "trait_decls" => traits,
            "trait_impls" => impls
        })

      removed = %{
        types: ids(Enum.filter(t["type_decls"], &pattern_item?/1)),
        traits:
          ids(Enum.filter(t["trait_decls"], &(&1 && pattern_item?(&1) && &1["def_id"] != id))),
        impls:
          ids(
            Enum.filter(
              t["trait_impls"],
              &(&1 && pattern_item?(&1) && &1["impl_trait"]["id"] != id)
            )
          ),
        functions:
          ids(
            Enum.filter(
              t["fun_decls"],
              &(&1 && pattern_item?(&1) && !MapSet.member?(kept, &1["def_id"]))
            )
          )
      }

      document =
        update_in(document, ["translated"], fn current ->
          Enum.reduce(
            [
              {"type_decls", :types},
              {"trait_decls", :traits},
              {"trait_impls", :impls},
              {"fun_decls", :functions}
            ],
            current,
            fn {key, family}, acc ->
              Map.update!(
                acc,
                key,
                &Enum.map(&1, fn d ->
                  if d && MapSet.member?(removed[family], d["def_id"]), do: nil, else: d
                end)
              )
            end
          )
        end)

      for key <- ~w(fun_decls type_decls trait_decls trait_impls global_decls),
          d <- document["translated"][key] || [],
          d do
        if observes_removed?(d, removed) or searcher?(d, id),
          do:
            raise(
              ArgumentError,
              "string prefix extraction cannot omit an observed foreign searcher definition"
            )
      end

      document =
        update_in(document, ["translated", "ordered_decls"], fn groups ->
          Enum.flat_map(groups, fn group ->
            [{kind, value}] = Map.to_list(group)

            family =
              %{
                "Fun" => :functions,
                "Type" => :types,
                "TraitDecl" => :traits,
                "TraitImpl" => :impls
              }[kind]

            removed_ids = removed[family] || MapSet.new()

            case value do
              %{"NonRec" => entity} ->
                if MapSet.member?(removed_ids, entity), do: [], else: [group]

              %{"Rec" => entities} ->
                kept_ids = Enum.reject(entities, &MapSet.member?(removed_ids, &1))
                if kept_ids == [], do: [], else: [%{kind => %{"Rec" => kept_ids}}]
            end
          end)
        end)

      document =
        update_in(document, ["translated", "assoc_item_names"], fn names ->
          List.update_at(names, id, fn row ->
            %{row | "types" => [], "methods" => ["is_prefix_of"]}
          end)
        end)

      projected = renumber(document, id)

      for f <- original_functions, f["def_id"] not in audit.library_helpers do
        after_f = find(projected["translated"]["fun_decls"], f["def_id"])

        unless Map.take(after_f, ~w(body signature)) == Map.take(f, ~w(body signature)),
          do:
            raise(
              ArgumentError,
              "string prefix projection changed a first-party body or signature"
            )
      end

      {projected,
       %{
         trait: id,
         method: @slot,
         implementations: Enum.filter(audit.library_helpers, &MapSet.member?(kept, &1))
       }}
    else
      {document, nil}
    end
  end

  defp ids(ds), do: MapSet.new(ds, & &1["def_id"])
  defp pattern_item?(nil), do: false
  defp pattern_item?(d), do: Enum.take(d["item_meta"]["name"], 3) == path(~w(core str pattern))

  defp observes_removed?(map, removed) when is_map(map) do
    direct =
      case map do
        %{"Adt" => %{"id" => id}} -> MapSet.member?(removed.types, id)
        %{"Fun" => id} -> MapSet.member?(removed.functions, id)
        %{"TraitImpl" => %{"id" => id}} -> MapSet.member?(removed.impls, id)
        %{"TraitMethod" => [id, _]} -> MapSet.member?(removed.traits, id)
        _ -> false
      end

    refs =
      Enum.any?(~w(trait_decl_ref trait_ref impl_trait), fn key ->
        value = map[key]
        is_map(value) && MapSet.member?(removed.traits, value["id"])
      end)

    bound =
      case map["trait_"] do
        %{"skip_binder" => %{"id" => id}} -> MapSet.member?(removed.traits, id)
        _ -> false
      end

    direct || refs || bound || Enum.any?(Map.values(map), &observes_removed?(&1, removed))
  end

  defp observes_removed?(list, r) when is_list(list),
    do: Enum.any?(list, &observes_removed?(&1, r))

  defp observes_removed?(_, _), do: false

  defp searcher?(%{"TraitType" => [raw, _, _]}, id),
    do: expand(raw, %{})["trait_decl_ref"]["id"] == id

  defp searcher?(map, id) when is_map(map), do: Enum.any?(Map.values(map), &searcher?(&1, id))
  defp searcher?(list, id) when is_list(list), do: Enum.any?(list, &searcher?(&1, id))
  defp searcher?(_, _), do: false

  defp renumber(map, id) when is_map(map) do
    map = Map.new(map, fn {k, v} -> {k, renumber(v, id)} end)

    map =
      if map["TraitMethod"] == [id, @slot], do: Map.put(map, "TraitMethod", [id, 0]), else: map

    map =
      case map["Trait"] do
        [raw, @slot] ->
          if expand(raw, %{})["trait_decl_ref"]["id"] == id,
            do: Map.put(map, "Trait", [raw, 0]),
            else: map

        _ ->
          map
      end

    if map["item_id"] == @slot && get_in(map, ["trait_ref", "id"]) == id,
      do: Map.put(map, "item_id", 0),
      else: map
  end

  defp renumber(list, id) when is_list(list), do: Enum.map(list, &renumber(&1, id))
  defp renumber(v, _), do: v

  defp trait(t, refs) do
    d = Enum.find(t["trait_decls"] || [], &(&1 && &1["item_meta"]["name"] == path(@path)))

    if d && d["src"] == "Normal" && d["is_unsafe"] == false && params?(d["generics"], 1, 0, 0) do
      m = Enum.at(d["methods"], @slot)
      sig = if m, do: expand(m["skip_binder"]["signature"], refs)

      if m && m["kind"] == %{"TraitMethod" => [d["def_id"], @slot]} &&
           m["skip_binder"]["name"] == "is_prefix_of" &&
           params?(m["params"], 0, 1, 0) && sig["abi"] == "Rust" && sig["is_unsafe"] == false &&
           sig["is_variadic"] == false &&
           sig["output"] == %{"Scalar" => "Bool"} &&
           match?([%{"TypeVar" => %{"Free" => 0}}, _], sig["inputs"]) do
        [_, input] = sig["inputs"]

        case input do
          %{"Ref" => [%{"Var" => %{"Bound" => [0, 0]}}, str, "Shared"]} ->
            if StringModels.borrowed_type?(ref(str, region(0)), t, refs), do: d["def_id"]

          _ ->
            nil
        end
      end
    end
  end

  defp safe?(f),
    do:
      match?(
        %{
          "body" => %{"Structured" => _},
          "signature" => %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false}
        },
        f
      )

  defp params?(p, types, regions, clauses),
    do:
      is_map(p) && Enum.map(p["types"], & &1["index"]) == indices(types) &&
        Enum.map(p["regions"], & &1["index"]) == indices(regions) && p["const_generics"] == [] &&
        p["trait_type_constraints"] == [] && p["outlives"] == [] &&
        length(p["trait_clauses"]) == clauses

  defp clause(b, refs), do: expand(b["trait_"]["skip_binder"], refs)
  defp decl(id, self), do: %{"id" => id, "generics" => args([self])}
  defp args(types, regions \\ []), do: ResourceModels.args(types) |> Map.put("regions", regions)
  defp ref(t, r), do: %{"Ref" => [r, t, "Shared"]}
  defp region(i), do: %{"Var" => %{"Free" => i}}
  defp var, do: %{"TypeVar" => %{"Free" => 0}}
  defp indices(0), do: []
  defp indices(n), do: Enum.to_list(0..(n - 1))
  defp path(xs), do: Enum.map(xs, &ident/1)
  defp ident(s), do: %{"Ident" => [s, 0]}
  defp find(xs, id), do: Enum.find(xs || [], &(&1 && &1["def_id"] == id))
  defp expand(v, refs), do: CallModels.expand(v, refs)

  defp reject!,
    do:
      raise(
        ArgumentError,
        "missing or unsupported shared-str prefix implementation or dictionary"
      )
end
