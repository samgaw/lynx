defmodule Lynx.Rust.OrderedIteratorModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, OrderedCollectionModels, ResourceModels}
  @source Path.expand("../../../priv/lean/LynxRustOrderedIterators.lean", __DIR__)
  @external_resource @source
  @contents File.read!(@source)

  def resolve(f, t, refs) do
    with %{"body" => "Opaque", "src" => %{"TraitImpl" => src}, "signature" => sig} <- f,
         true <- safe?(sig),
         false <- src["reuses_default"],
         0 <- src["item_id"],
         [
           a,
           b,
           c,
           %{"Ident" => [family, 0]},
           %{"Impl" => %{"Trait" => impl_id}},
           %{"Ident" => [method, 0]}
         ] <- f["item_meta"]["name"],
         true <- [a, b, c] == path(~w(alloc collections btree)),
         true <- family in ~w(map set) and method in ~w(into_iter next),
         ctx = context(t, refs),
         n = if(family == "map", do: 2, else: 1),
         iterator when is_integer(iterator) <- ctx.iterators[family],
         true <- iterator_type?(find(t["type_decls"], iterator), family, refs),
         %{"src" => "Normal", "is_unsafe" => false, "is_negative" => false} = impl <-
           find(t["trait_impls"], impl_id),
         true <-
           impl["item_meta"]["name"] ==
             path(["alloc", "collections", "btree", family]) ++
               [%{"Impl" => %{"Trait" => impl_id}}],
         true <- impl["consts"] == [] and Enum.all?(impl["types"], &is_nil/1),
         true <- src["impl_ref"]["id"] == impl_id,
         trait_id = if(method == "next", do: ctx.next, else: ctx.into),
         trait when is_map(trait) <- find(t["trait_decls"], trait_id),
         true <- trait["src"] == "Normal" and trait["is_unsafe"] == false,
         true <- params?(trait["generics"], if(method == "next", do: 2, else: 3), 0, [], []),
         count = if(method == "next", do: n, else: n + 1),
         clauses = if(method == "next", do: [], else: allocator_clause(count - 1, ctx)),
         true <-
           params?(
             CallModels.expand(impl["generics"], refs),
             count,
             1,
             type_bounds(count, 0),
             clauses
           ),
         true <- Enum.map(impl["generics"]["regions"], & &1["late_bound"]) == [false],
         true <-
           params?(
             CallModels.expand(f["generics"], refs),
             count,
             if(method == "next", do: 2, else: 1),
             if(method == "next",
               do: type_bounds(n, 0) ++ [bound(region(0), region(1))] ++ type_bounds(n, 1),
               else: type_bounds(count, 0)
             ),
             clauses
           ),
         true <-
           Enum.map(f["generics"]["regions"], & &1["late_bound"]) ==
             if(method == "next", do: [false, true], else: [false]),
         iter = adt(iterator, variables(n), [region(0)]),
         item = item(family, region(0)),
         collection = adt(ctx.collections[family], variables(count)),
         implemented =
           if(method == "next",
             do: args([iter, item]),
             else: args([ref(collection, region(0), "Shared"), item, iter])
           ),
         true <-
           CallModels.expand(src["trait_ref"], refs) == %{
             "id" => trait_id,
             "generics" => implemented
           },
         true <-
           CallModels.expand(impl["impl_trait"], refs) == %{
             "id" => trait_id,
             "generics" => implemented
           },
         true <- forwarded?(src["impl_ref"]["generics"], count, [region(0)], method, ctx),
         %{
           "kind" => %{"TraitMethod" => [^trait_id, 0]},
           "params" => method_params,
           "skip_binder" => pointer
         } <- Enum.at(impl["methods"], 0),
         true <- pointer["id"] == f["def_id"],
         true <- params?(method_params, 0, if(method == "next", do: 1, else: 0), [], []),
         true <-
           forwarded?(
             pointer["generics"],
             count,
             if(method == "next",
               do: [region(0), %{"Var" => %{"Bound" => [0, 0]}}],
               else: [region(0)]
             ),
             method,
             ctx
           ),
         true <-
           if(method == "next",
             do:
               CallModels.expand(sig["inputs"], refs) == [ref(iter, region(1), "Mut")] and
                 option?(CallModels.expand(sig["output"], refs), item, t, refs) and
                 impl["implied_trait_refs"] == [],
             else:
               CallModels.expand(sig["inputs"], refs) == [ref(collection, region(0), "Shared")] and
                 CallModels.expand(sig["output"], refs) == iter and length(impl["methods"]) == 1 and
                 next_dependency?(impl, family, iter, n, ctx)
           ) do
      %{
        rust_name: "alloc::collections::btree::#{family}::_::#{method}",
        lean: "OrderedIterators." <> family <> if(method == "next", do: "Next", else: "IntoIter"),
        ordered_iterator: family,
        ordered_iterator_method: method,
        iterator_type_id: iterator,
        builtin: false,
        can_fail: true,
        lift: true,
        native_cutoff_only: true,
        keep_params: List.duplicate(false, count),
        keep_trait_clauses: List.duplicate(false, length(clauses)),
        model_digest: Lynx.Rust.Fingerprint.digest(@contents),
        label:
          "Shared ordered #{family} iterator model: numeric u64 entries in ascending order, finite cursor and stable exhaustion; 262144-entry bound is verification exhaustion; native std traversal, borrowed pointers/layout, allocation and lifetime correspondence remain unverified"
      }
    else
      _ -> nil
    end
  end

  defp next_dependency?(impl, family, iter, n, ctx) do
    with [raw] <- impl["implied_trait_refs"],
         %{
           "kind" => %{"TraitImpl" => %{"id" => id, "generics" => generics}},
           "trait_decl_ref" => declared
         } <- dictionary(raw, ctx),
         true <- CallModels.expand(generics, ctx.refs) == args(variables(n), ["Erased"]),
         true <-
           CallModels.expand(declared, ctx.refs) == %{
             "id" => ctx.next,
             "generics" => args([iter, item(family, "Erased")])
           },
         next when is_map(next) <- find(ctx.t["trait_impls"], id),
         f when is_map(f) <-
           find(ctx.t["fun_decls"], Enum.at(next["methods"], 0)["skip_binder"]["id"]),
         %{ordered_iterator: ^family, ordered_iterator_method: "next"} <-
           resolve(f, ctx.t, ctx.refs) do
      true
    else
      _ -> false
    end
  end

  defp forwarded?(g, count, regions, method, ctx) do
    CallModels.expand(g["types"], ctx.refs) == variables(count) and
      g["regions"] == regions and g["const_generics"] == [] and
      if method == "next" do
        g["trait_refs"] == []
      else
        case g["trait_refs"] do
          [raw] ->
            case dictionary(raw, ctx) do
              %{
                "kind" => %{"Clause" => [%{"Free" => 0}, %{"regions" => []}]},
                "trait_decl_ref" => declared
              } ->
                CallModels.expand(declared, ctx.refs) == %{
                  "id" => ctx.collections.traits["AllocatorClone"],
                  "generics" => args([var(count - 1)])
                }

              _ ->
                false
            end

          _ ->
            false
        end
      end
  end

  def context(t, refs) do
    iterators =
      for family <- ~w(map set), into: %{} do
        decl =
          Enum.find(
            t["type_decls"] || [],
            &(&1 &&
                &1["item_meta"]["name"] == path(["alloc", "collections", "btree", family, "Iter"]))
          )

        {family, if(decl, do: decl["def_id"])}
      end

    traits =
      for {key, name} <- [
            {:next, ~w(core iter traits iterator Iterator)},
            {:into, ~w(core iter traits collect IntoIterator)}
          ],
          into: %{} do
        decl = Enum.find(t["trait_decls"] || [], &(&1 && &1["item_meta"]["name"] == path(name)))
        {key, if(decl, do: decl["def_id"])}
      end

    Map.merge(traits, %{
      iterators: iterators,
      t: t,
      refs: refs,
      dictionaries: ResourceModels.trait_references(t),
      collections: OrderedCollectionModels.context(t, refs)
    })
  end

  def audit(functions, models, t, refs, first_party, _execution) do
    ctx = context(t, refs)

    if Enum.all?(Map.values(ctx.iterators), &is_nil/1) do
      {:ok, %{families: []}}
    else
      data = functions ++ Enum.filter(t["type_decls"] || [], &first_party?(&1, first_party))

      Enum.reduce_while(data, {:ok, []}, fn owner, {:ok, used} ->
        try do
          types = types!(owner, ctx)

          calls!(owner["body"], models, ctx)
          {:cont, {:ok, Enum.uniq(used ++ types)}}
        rescue
          e in ArgumentError -> {:halt, {:error, owner, Exception.message(e)}}
        end
      end)
      |> case do
        {:ok, families} -> {:ok, %{families: families}}
        failure -> failure
      end
    end
  end

  defp types!(%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => g}}, ctx) do
    family = Enum.find(~w(map set), &(ctx.iterators[&1] == id))

    if family do
      n = if family == "map", do: 2, else: 1

      unless iterator_type?(find(ctx.t["type_decls"], id), family, ctx.refs) and
               CallModels.expand(g["types"], ctx.refs) == List.duplicate(u64(), n) and
               length(g["regions"]) == 1 and g["const_generics"] == [] and g["trait_refs"] == [],
             do:
               raise(
                 ArgumentError,
                 "unsupported ordered iterator representation; only shared concrete u64 entries are modelled"
               )

      [family]
    else
      types!(g, ctx)
    end
  end

  defp types!(m, ctx) when is_map(m),
    do:
      Enum.flat_map(m, fn
        {key, value} when key in ~w(ty inputs output) ->
          types!(CallModels.expand(value, ctx.refs), ctx)

        {_, value} ->
          types!(value, ctx)
      end)

  defp types!(l, ctx) when is_list(l), do: Enum.flat_map(l, &types!(&1, ctx))
  defp types!(_, _), do: []

  defp calls!(%{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => g}}, models, ctx) do
    model = models[id]

    if model && model[:ordered_iterator] do
      n = if model.ordered_iterator == "map", do: 2, else: 1
      into? = model.ordered_iterator_method == "into_iter"

      expected =
        List.duplicate(u64(), n) ++ if(into?, do: [adt(ctx.collections.global, [])], else: [])

      unless CallModels.expand(g["types"], ctx.refs) == expected and g["const_generics"] == [] and
               length(g["regions"]) == if(into?, do: 1, else: 2),
             do:
               raise(
                 ArgumentError,
                 "ordered iterator calls require concrete u64 entries and standard Global allocation"
               )

      if into? do
        case g["trait_refs"] do
          [raw] -> OrderedCollectionModels.allocator_dictionary!(raw, ctx.t, ctx.refs)
          _ -> raise ArgumentError, "missing ordered iterator allocator dictionary"
        end
      else
        unless g["trait_refs"] == [],
          do: raise(ArgumentError, "unexpected ordered iterator next dictionary")
      end
    end
  end

  defp calls!(m, models, ctx) when is_map(m),
    do: Enum.each(Map.values(m), &calls!(&1, models, ctx))

  defp calls!(l, models, ctx) when is_list(l), do: Enum.each(l, &calls!(&1, models, ctx))
  defp calls!(_, _, _), do: :ok

  def scope(audit, prefix) do
    %{
      audit
      | external_calls:
          Map.new(audit.external_calls, fn {id, m} ->
            if m[:ordered_iterator], do: {id, %{m | lean: prefix <> "." <> m.lean}}, else: {id, m}
          end)
    }
  end

  def external_names(audit, prefix) do
    case audit.ordered_iterators.families do
      [] ->
        %{}

      families ->
        %{
          "types" =>
            for family <- families do
              %{
                "rust_pattern" => "alloc::collections::btree::#{family}::Iter",
                "extract_name" =>
                  prefix <> ".OrderedIterators." <> String.capitalize(family) <> "Iterator",
                "keep_params" => List.duplicate(false, if(family == "map", do: 2, else: 1))
              }
            end
        }
    end
  end

  def install!(audit, output, prefix) do
    if audit.ordered_iterators.families == [] do
      []
    else
      name = prefix <> ".OrderedIteratorsModel"
      path = Path.join(output, String.replace(name, ".", "/") <> ".lean")
      File.mkdir_p!(Path.dirname(path))
      File.write!(path, String.replace(@contents, "__PREFIX__", prefix))
      [name]
    end
  end

  def boundaries(audit) do
    for family <- Map.get(audit, :ordered_iterators, %{families: []}).families do
      "Shared ordered #{family} iteration model: finite ascending u64 cursor; native std traversal, borrowed pointer/layout/lifetime correspondence remain unverified; entry/key-domain limits exhaust verification rather than native rejection"
    end
  end

  defp iterator_type?(
         %{
           "src" => "Normal",
           "kind" => "Opaque",
           "item_meta" => %{"name" => name},
           "generics" => params
         },
         family,
         refs
       ) do
    n = if family == "map", do: 2, else: 1

    bounds =
      if family == "map", do: type_bounds(n, 0), else: type_bounds(n, 0) ++ type_bounds(n, 0)

    name == path(["alloc", "collections", "btree", family, "Iter"]) and
      params?(CallModels.expand(params, refs), n, 1, bounds, []) and
      Enum.map(params["regions"], &Map.take(&1, ~w(index late_bound mutability))) == [
        %{"index" => 0, "late_bound" => false, "mutability" => "Shared"}
      ]
  end

  defp iterator_type?(_, _, _), do: false

  defp allocator_clause(index, ctx),
    do: [
      {0, %{"id" => ctx.collections.traits["AllocatorClone"], "generics" => args([var(index)])}}
    ]

  defp params?(p, n, r, bounds, clauses) do
    (p["types"] && Enum.map(p["types"], & &1["index"]) == indices(n)) and
      Enum.map(p["regions"], & &1["index"]) == indices(r) and p["const_generics"] == [] and
      p["trait_type_constraints"] == [] and p["outlives"] == bounds and
      Enum.map(p["trait_clauses"], fn c ->
        if c["trait_"]["regions"] == [] and c["trait_"]["outlives"] == [],
          do: {c["clause_id"], c["trait_"]["skip_binder"]},
          else: :unsupported
      end) == clauses
  end

  defp item("map", r),
    do: %{
      "Adt" => %{
        "id" => 0,
        "builtin" => "Tuple",
        "generics" => args([ref(var(0), r, "Shared"), ref(var(1), r, "Shared")])
      }
    }

  defp item("set", r), do: ref(var(0), r, "Shared")

  defp option?(%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => g}}, item, t, refs),
    do: g == args([item]) and Lynx.Rust.OptionModels.option_type?(find(t["type_decls"], id), refs)

  defp option?(_, _, _, _), do: false

  defp safe?(s) when is_map(s),
    do:
      Map.take(s, ~w(abi is_unsafe is_variadic)) == %{
        "abi" => "Rust",
        "is_unsafe" => false,
        "is_variadic" => false
      }

  defp safe?(_), do: false

  defp first_party?(%{"item_meta" => %{"name" => [%{"Ident" => [name, 0]} | _]}}, names),
    do: name in names

  defp first_party?(_, _), do: false
  defp type_bounds(n, r), do: Enum.map(variables(n), &bound(%{"Lub" => &1}, region(r)))
  defp bound(a, b), do: %{"regions" => [], "outlives" => [], "skip_binder" => [a, b]}
  defp region(n), do: %{"Var" => %{"Free" => n}}
  defp ref(type, r, mode), do: %{"Ref" => [r, type, mode]}

  defp adt(id, types, regions \\ []),
    do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args(types, regions)}}

  defp args(types, regions \\ []), do: ResourceModels.args(types, [], regions)
  defp dictionary(raw, ctx), do: ResourceModels.dictionary(raw, ctx.dictionaries)
  defp u64, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}
  defp var(n), do: %{"TypeVar" => %{"Free" => n}}
  defp variables(n), do: Enum.map(indices(n), &var/1)
  defp indices(0), do: []
  defp indices(n), do: Enum.to_list(0..(n - 1))
  defp path(names), do: Enum.map(names, &%{"Ident" => [&1, 0]})
  defp find(rows, id), do: Enum.find(rows || [], &(&1 && &1["def_id"] == id))
end
