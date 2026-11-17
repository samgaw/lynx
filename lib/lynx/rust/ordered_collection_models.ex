defmodule Lynx.Rust.OrderedCollectionModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, OptionModels, ResourceModels}
  @source Path.expand("../../../priv/lean/LynxRustOrderedCollections.lean", __DIR__)
  @external_resource @source
  @contents File.read!(@source)
  @families %{"map" => {"BTreeMap", 3}, "set" => {"BTreeSet", 2}}

  def resolve(f, t, refs) do
    with %{"src" => "Normal", "body" => "Opaque", "signature" => sig} <- f,
         true <-
           Map.take(sig, ~w(abi is_unsafe is_variadic)) == %{
             "abi" => "Rust",
             "is_unsafe" => false,
             "is_variadic" => false
           },
         [
           a,
           b,
           c,
           %{"Ident" => [family, 0]},
           %{"Impl" => %{"Ty" => parent}},
           %{"Ident" => [method, 0]}
         ] <- f["item_meta"]["name"],
         true <- [a, b, c] == path(~w(alloc collections btree)),
         {_, count} <- @families[family],
         true <-
           method in ~w(new insert len remove) or
             {family, method} in [{"map", "get"}, {"set", "contains"}],
         ctx = context(t, refs),
         id when is_integer(id) <- ctx[family],
         true <- type?(find(t["type_decls"], id), family),
         true <- global?(ctx.global, t),
         query? = method in ~w(get contains remove),
         n = if(method == "new", do: count - 1, else: count + if(query?, do: 1, else: 0)),
         p = free(CallModels.expand(parent, refs)),
         true <- p["kind"] == "InherentImplBlock",
         true <-
           params?(
             p["params"],
             if(query?, do: count, else: n),
             0,
             if(method == "new", do: 0, else: 1)
           ),
         true <-
           params?(
             CallModels.expand(f["generics"], refs),
             n,
             if(method == "new", do: 0, else: if(query?, do: 2, else: 1)),
             if(method == "new",
               do: 0,
               else: if(query?, do: 4, else: if(method == "insert", do: 2, else: 1))
             ),
             query?
           ),
         self = adt(id, Enum.map(indices(count), &var/1)),
         self =
           if(method == "new",
             do:
               put_in(
                 self,
                 ["Adt", "generics", "types"],
                 Enum.map(indices(n), &var/1) ++ [adt(ctx.global, [])]
               ),
             else: self
           ),
         true <- p["skip_binder"] == self,
         true <- clauses?(p["params"], method, false, if(query?, do: count, else: n), ctx),
         true <- clauses?(CallModels.expand(f["generics"], refs), method, true, n, ctx),
         true <- signature?(CallModels.expand(sig, refs), family, method, self, t, refs) do
      operation = family <> String.capitalize(method)

      %{
        rust_name: "alloc::collections::btree::#{family}::_::#{method}",
        lean: "OrderedCollections." <> operation,
        ordered_collection: family,
        ordered_method: method,
        builtin: false,
        keep_params: List.duplicate(false, n),
        keep_trait_clauses: List.duplicate(false, length(f["generics"]["trait_clauses"])),
        can_fail: method != "new",
        lift: method != "new",
        native_cutoff_only: method != "new",
        model_digest: Lynx.Rust.Fingerprint.digest(@contents),
        label:
          "Ordered #{family} semantic model: only u64 keys/values and the resolved standard u64 Ord/identity Borrow/Global allocator are admitted; at most 262144 distinct entries; exceeding the bound exhausts verification, not Rust rejection; std tree implementation, layout, allocation/failure and deallocation remain unverified"
      }
    else
      _ -> nil
    end
  end

  def context(t, refs) do
    ids =
      for {family, {name, _}} <- @families, into: %{} do
        d =
          Enum.find(
            t["type_decls"] || [],
            &(&1 &&
                &1["item_meta"]["name"] == path(["alloc", "collections", "btree", family, name]))
          )

        {family, if(d, do: d["def_id"])}
      end

    global =
      Enum.find(
        t["type_decls"] || [],
        &(&1 && &1["item_meta"]["name"] == path(~w(alloc alloc Global)))
      )

    traits =
      Map.new(~w(Ord AllocatorClone Borrow), fn name ->
        p =
          case name do
            "Ord" -> ~w(core cmp Ord)
            "Borrow" -> ~w(core borrow Borrow)
            "AllocatorClone" -> ~w(core alloc AllocatorClone)
          end

        d = Enum.find(t["trait_decls"] || [], &(&1 && &1["item_meta"]["name"] == path(p)))
        {name, if(d, do: d["def_id"])}
      end)

    Map.merge(ids, %{global: if(global, do: global["def_id"]), traits: traits, t: t, refs: refs})
  end

  def audit(functions, models, t, refs, first_party, execution) do
    ctx = context(t, refs)
    data = functions ++ Enum.filter(t["type_decls"] || [], &(&1 && local?(&1, first_party)))

    if is_nil(ctx["map"]) and is_nil(ctx["set"]) do
      {:ok, %{families: [], types: %{}}}
    else
      Enum.reduce_while(data, {:ok, []}, fn item, {:ok, used} ->
        try do
          found = type_uses(item, ctx)

          if found != [] and execution != :pure,
            do: raise(ArgumentError, "ordered collections currently require pure Rust extraction")

          if Map.has_key?(item, "body"), do: calls!(item["body"], item, models, ctx)
          {:cont, {:ok, Enum.uniq(used ++ found)}}
        rescue
          e in ArgumentError -> {:halt, {:error, item, Exception.message(e)}}
        end
      end)
      |> case do
        {:ok, used} -> {:ok, %{families: used, types: Map.take(ctx, used)}}
        error -> error
      end
    end
  end

  defp calls!(%{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => g}}, _owner, models, ctx) do
    model = models[id]

    if model && model[:ordered_collection] do
      family = model.ordered_collection
      expected = if family == "map", do: [u64(), u64()], else: [u64()]

      expected =
        if model.ordered_method == "new", do: expected, else: expected ++ [adt(ctx.global, [])]

      query? = model.ordered_method in ~w(get contains remove)
      expected = if query?, do: expected ++ [u64()], else: expected

      unless CallModels.expand(g["types"], ctx.refs) == expected and g["const_generics"] == [] and
               length(g["regions"]) ==
                 if(model.ordered_method == "new", do: 0, else: if(query?, do: 2, else: 1)),
             do:
               raise(
                 ArgumentError,
                 "ordered collections require concrete u64 entries and the standard Global allocator"
               )

      names =
        if model.ordered_method == "new",
          do: [],
          else:
            if(query?,
              do: ~w(AllocatorClone Borrow Ord Ord),
              else:
                if(model.ordered_method == "insert",
                  do: ~w(AllocatorClone Ord),
                  else: ~w(AllocatorClone)
                )
            )

      unless length(g["trait_refs"]) == length(names),
        do: raise(ArgumentError, "missing ordered collection dictionaries")

      for {name, raw} <- Enum.zip(names, g["trait_refs"]) do
        if name == "Borrow", do: borrow_dictionary!(raw, ctx), else: dictionary!(name, raw, ctx)
      end
    end
  end

  defp calls!(m, f, models, ctx) when is_map(m),
    do: Enum.each(Map.values(m), &calls!(&1, f, models, ctx))

  defp calls!(l, f, models, ctx) when is_list(l), do: Enum.each(l, &calls!(&1, f, models, ctx))
  defp calls!(_, _, _, _), do: :ok

  def borrow_helper?(f, t) do
    ctx = context(t, Lynx.Rust.LLBC.type_references!(t))
    id = f["src"]["TraitImpl"]["impl_ref"]["id"]
    impl = find(t["trait_impls"], id)

    if impl && Enum.any?(impl["methods"], &(&1["skip_binder"]["id"] == f["def_id"])) do
      raw = %{
        "regions" => [],
        "outlives" => [],
        "skip_binder" => %{
          "Value" => [
            0,
            %{
              "kind" => %{"TraitImpl" => %{"id" => id, "generics" => args([u64()])}},
              "trait_decl_ref" => %{
                "id" => ctx.traits["Borrow"],
                "generics" => args([u64(), u64()])
              }
            }
          ]
        }
      }

      try do
        borrow_dictionary!(raw, ctx)
        true
      rescue
        ArgumentError -> false
      end
    else
      false
    end
  end

  defp borrow_dictionary!(raw, ctx) do
    trait = ctx.traits["Borrow"]

    with %{
           "kind" => %{"TraitImpl" => %{"id" => id, "generics" => g}},
           "trait_decl_ref" => declared
         } <-
           ResourceModels.dictionary(raw, ResourceModels.trait_references(ctx.t)),
         true <- CallModels.expand(g, ctx.refs) == args([u64()]),
         true <-
           CallModels.expand(declared, ctx.refs) == %{
             "id" => trait,
             "generics" => args([u64(), u64()])
           },
         %{"src" => "Normal", "is_unsafe" => false, "is_negative" => false} = impl <-
           find(ctx.t["trait_impls"], id),
         true <-
           impl["item_meta"]["name"] == path(~w(core borrow)) ++ [%{"Impl" => %{"Trait" => id}}],
         true <- params?(impl["generics"], 1, 0, 0),
         true <-
           CallModels.expand(impl["impl_trait"], ctx.refs) == %{
             "id" => trait,
             "generics" => args([var(0), var(0)])
           },
         true <- impl["types"] == [] and impl["consts"] == [] and impl["implied_trait_refs"] == [],
         %{"src" => "Normal", "is_unsafe" => false} = d <- find(ctx.t["trait_decls"], trait),
         true <- params?(d["generics"], 2, 0, 0),
         [declared_method] <- d["methods"],
         true <- declared_method["kind"] == %{"TraitMethod" => [trait, 0]},
         true <- params?(declared_method["params"], 0, 1, 0),
         true <- declared_method["skip_binder"]["name"] == "borrow",
         true <- is_nil(declared_method["skip_binder"]["default"]),
         true <-
           CallModels.expand(declared_method["skip_binder"]["signature"], ctx.refs) == %{
             "abi" => "Rust",
             "is_unsafe" => false,
             "is_variadic" => false,
             "inputs" => [%{"Ref" => [%{"Var" => %{"Bound" => [0, 0]}}, var(0), "Shared"]}],
             "output" => %{"Ref" => [%{"Var" => %{"Bound" => [0, 0]}}, var(1), "Shared"]}
           },
         [
           %{
             "kind" => %{"TraitMethod" => [^trait, 0]},
             "params" => params,
             "skip_binder" => pointer
           }
         ] <- impl["methods"],
         true <- params?(params, 0, 1, 0),
         true <-
           CallModels.expand(pointer["generics"], ctx.refs) ==
             Map.put(args([var(0)]), "regions", [%{"Var" => %{"Bound" => [0, 0]}}]),
         f when is_map(f) <- find(ctx.t["fun_decls"], pointer["id"]),
         true <- f["item_meta"]["name"] == impl["item_meta"]["name"] ++ path(["borrow"]),
         true <-
           f["src"]["TraitImpl"]["impl_ref"]["id"] == id and f["src"]["TraitImpl"]["item_id"] == 0,
         true <-
           CallModels.expand(f["src"]["TraitImpl"]["impl_ref"]["generics"], ctx.refs) ==
             args([var(0)]),
         true <-
           CallModels.expand(f["src"]["TraitImpl"]["trait_ref"], ctx.refs) == %{
             "id" => trait,
             "generics" => args([var(0), var(0)])
           },
         true <- f["src"]["TraitImpl"]["reuses_default"] == false,
         true <- params?(CallModels.expand(f["generics"], ctx.refs), 1, 1, 0),
         true <-
           CallModels.expand(f["signature"], ctx.refs) == %{
             "abi" => "Rust",
             "is_unsafe" => false,
             "is_variadic" => false,
             "inputs" => [ref(var(0), "Shared")],
             "output" => ref(var(0), "Shared")
           } do
      :ok
    else
      _ ->
        raise ArgumentError,
              "unsupported ordered collection Borrow dictionary; only the standard identity borrow of u64 is modelled"
    end
  end

  def allocator_dictionary!(raw, t, refs),
    do: dictionary!("AllocatorClone", raw, context(t, refs))

  defp dictionary!(name, raw, ctx) do
    expected = if name == "Ord", do: u64(), else: adt(ctx.global, [])

    with %{
           "kind" => %{"TraitImpl" => %{"id" => id, "generics" => g}},
           "trait_decl_ref" => declared
         } <- ResourceModels.dictionary(raw, ResourceModels.trait_references(ctx.t)),
         true <- g == args([]),
         %{"src" => "Normal", "is_negative" => false} = impl <-
           find(ctx.t["trait_impls"], id),
         true <- impl["is_unsafe"] == (name == "AllocatorClone"),
         true <- params?(impl["generics"], 0, 0, 0),
         prefix = if(name == "Ord", do: ~w(core cmp impls), else: ~w(alloc alloc)),
         true <- impl["item_meta"]["name"] == path(prefix) ++ [%{"Impl" => %{"Trait" => id}}],
         true <-
           CallModels.expand(declared, ctx.refs) == %{
             "id" => ctx.traits[name],
             "generics" => args([expected])
           },
         true <-
           CallModels.expand(impl["impl_trait"], ctx.refs) ==
             CallModels.expand(declared, ctx.refs) do
      unless comparison_or_allocator?(name, impl, ctx),
        do: raise(ArgumentError, "incomplete standard #{name} ordered collection dictionary")

      :ok
    else
      _ ->
        raise ArgumentError,
              "unsupported #{name} dictionary for ordered collection; custom ordering and allocators are not modelled"
    end
  end

  defp comparison_or_allocator?("Ord", impl, ctx) do
    trait = ctx.traits["Ord"]
    d = find(ctx.t["trait_decls"], trait)

    with true <- d["src"] == "Normal" and d["is_unsafe"] == false,
         true <- params?(d["generics"], 1, 0, 0),
         %{
           "kind" => %{"TraitMethod" => [^trait, 0]},
           "params" => p,
           "skip_binder" => %{"id" => id, "generics" => g}
         } <- Enum.at(impl["methods"], 0),
         true <- params?(p, 0, 2, 0),
         true <-
           CallModels.expand(g, ctx.refs) ==
             Map.put(args([]), "regions", [
               %{"Var" => %{"Bound" => [0, 0]}},
               %{"Var" => %{"Bound" => [0, 1]}}
             ]),
         f when is_map(f) <- find(ctx.t["fun_decls"], id),
         true <-
           f["src"]["TraitImpl"]["impl_ref"]["id"] == impl["def_id"] and
             f["src"]["TraitImpl"]["item_id"] == 0,
         true <- f["item_meta"]["name"] == impl["item_meta"]["name"] ++ path(["cmp"]),
         true <- params?(CallModels.expand(f["generics"], ctx.refs), 0, 2, 0),
         %{"Adt" => %{"id" => ordering, "builtin" => nil, "generics" => a}} <-
           CallModels.expand(f["signature"]["output"], ctx.refs),
         true <- a == args([]),
         %{
           "src" => "Normal",
           "item_meta" => %{"name" => name},
           "generics" => op,
           "kind" => kind
         } <- find(ctx.t["type_decls"], ordering),
         true <- name == path(~w(core cmp Ordering)) and params?(op, 0, 0, 0),
         true <-
           kind == "Opaque" or
             (match?(%{"Enum" => _}, kind) and
                Enum.map(kind["Enum"], &Map.take(&1, ~w(name fields))) ==
                  Enum.map(~w(Less Equal Greater), &%{"name" => &1, "fields" => []})),
         sig = CallModels.expand(f["signature"], ctx.refs),
         true <-
           Map.take(sig, ~w(abi is_unsafe is_variadic inputs)) == %{
             "abi" => "Rust",
             "is_unsafe" => false,
             "is_variadic" => false,
             "inputs" => [
               ref(u64(), "Shared"),
               %{"Ref" => [%{"Var" => %{"Free" => 1}}, u64(), "Shared"]}
             ]
           } do
      true
    else
      _ -> false
    end
  end

  defp comparison_or_allocator?("AllocatorClone", impl, ctx) do
    trait = find(ctx.t["trait_decls"], ctx.traits["AllocatorClone"])

    with true <- trait["src"] == "Normal" and trait["is_unsafe"] == true,
         true <- params?(trait["generics"], 1, 0, 0),
         true <- impl["methods"] == [] and impl["types"] == [] and impl["consts"] == [],
         [raw] <- impl["implied_trait_refs"],
         %{
           "kind" => %{"TraitImpl" => %{"id" => id, "generics" => g}},
           "trait_decl_ref" => declared
         } <- ResourceModels.dictionary(raw, ResourceModels.trait_references(ctx.t)),
         true <- g == args([]),
         %{"src" => "Normal", "is_unsafe" => false, "is_negative" => false} = clone <-
           find(ctx.t["trait_impls"], id),
         true <-
           clone["item_meta"]["name"] == path(~w(alloc alloc)) ++ [%{"Impl" => %{"Trait" => id}}],
         true <- params?(clone["generics"], 0, 0, 0),
         %{"item_meta" => %{"name" => clone_name}} <- find(ctx.t["trait_decls"], declared["id"]),
         true <- clone_name == path(~w(core clone Clone)),
         true <- CallModels.expand(declared["generics"], ctx.refs) == args([adt(ctx.global, [])]),
         true <-
           CallModels.expand(clone["impl_trait"], ctx.refs) ==
             CallModels.expand(declared, ctx.refs) do
      true
    else
      _ -> false
    end
  end

  defp type_uses(%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => g}}, ctx) do
    family = Enum.find(Map.keys(@families), &(ctx[&1] == id))

    if family do
      expected = if family == "map", do: [u64(), u64()], else: [u64()]

      unless type?(find(ctx.t["type_decls"], id), family) and global?(ctx.global, ctx.t) and
               CallModels.expand(g, ctx.refs) == args(expected ++ [adt(ctx.global, [])]),
             do:
               raise(
                 ArgumentError,
                 "unsupported ordered collection representation; only concrete u64 entries and Global are admitted"
               )

      [family]
    else
      type_uses(g, ctx)
    end
  end

  defp type_uses(m, ctx) when is_map(m) do
    Enum.flat_map(m, fn
      {key, v} when key in ~w(ty inputs output) -> type_uses(CallModels.expand(v, ctx.refs), ctx)
      {_, v} -> type_uses(v, ctx)
    end)
  end

  defp type_uses(l, ctx) when is_list(l), do: Enum.flat_map(l, &type_uses(&1, ctx))
  defp type_uses(_, _), do: []

  def scope(audit, prefix) do
    %{
      audit
      | external_calls:
          Map.new(audit.external_calls, fn {id, model} ->
            if model[:ordered_collection],
              do:
                {id,
                 %{
                   model
                   | lean:
                       prefix <>
                         ".OrderedCollections." <>
                         model.ordered_collection <> String.capitalize(model.ordered_method)
                 }},
              else: {id, model}
          end)
    }
  end

  def boundaries(audit) do
    for family <- Map.get(audit, :ordered_collections, %{families: []}).families do
      "Ordered #{family} representation model: concrete u64 keys/values mapped to Lean Std.TreeMap/TreeSet with numeric ordering; native std tree structure, allocator, layout and lifetime correspondence are unverified; mutating/length operations enforce the explicit entry bound"
    end
  end

  def external_names(audit, prefix) do
    types =
      for family <- audit.ordered_collections.families do
        {name, count} = @families[family]

        %{
          "rust_pattern" => "alloc::collections::btree::#{family}::#{name}",
          "extract_name" => prefix <> ".OrderedCollections." <> String.capitalize(family),
          "keep_params" => List.duplicate(false, count)
        }
      end

    if types == [], do: %{}, else: %{"types" => types}
  end

  def install!(audit, output, prefix) do
    if audit.ordered_collections.families == [] and
         Map.get(audit, :ordered_iterators, %{families: []}).families == [] do
      []
    else
      name = prefix <> ".OrderedCollectionsModel"
      path = Path.join(output, String.replace(name, ".", "/") <> ".lean")
      File.mkdir_p!(Path.dirname(path))
      File.write!(path, String.replace(@contents, "__PREFIX__", prefix))
      [name]
    end
  end

  def family(type, t, refs) do
    ctx = context(t, refs)

    case CallModels.expand(type, refs) do
      %{"Adt" => %{"id" => id, "builtin" => nil}} ->
        Enum.find(Map.keys(@families), &(ctx[&1] == id))

      _ ->
        nil
    end
  end

  def drop_site!(drop, t, refs) do
    ctx = context(t, refs)

    with %{
           "kind" => kind,
           "place" => %{"ty" => annotation},
           "fn_ptr" => %{"kind" => %{"Fun" => id}, "generics" => g}
         } <- drop,
         true <- kind in ["Precise", "Conditional"],
         self = CallModels.expand(annotation, refs),
         [family] <- type_uses(self, ctx),
         {type_name, count} = @families[family],
         true <-
           length(g["regions"]) == 1 and match?([%{"Body" => n}] when is_integer(n), g["regions"]),
         true <- CallModels.expand(g["types"], refs) == self["Adt"]["generics"]["types"],
         true <- g["const_generics"] == [],
         [dictionary] <- g["trait_refs"],
         :ok <- dictionary!("AllocatorClone", dictionary, ctx),
         f when is_map(f) <- find(t["fun_decls"], id),
         %{
           "TraitImpl" => %{
             "impl_ref" => %{"id" => impl_id, "generics" => inherited},
             "trait_ref" => trait,
             "item_id" => 0,
             "reuses_default" => false
           }
         } <- f["src"],
         variables = Enum.map(indices(count), &var/1),
         parent = adt(ctx[family], variables),
         true <-
           f["body"] == "Opaque" and
             f["item_meta"]["name"] ==
               path(["alloc", "collections", "btree", family, type_name]) ++
                 [%{"Impl" => %{"Trait" => impl_id}}, %{"Builtin" => ["DropGlue", 0]}],
         true <- params?(CallModels.expand(f["generics"], refs), count, 1, 1),
         true <- clauses?(CallModels.expand(f["generics"], refs), "len", true, count, ctx),
         true <-
           CallModels.expand(f["signature"], refs) == %{
             "abi" => "Rust",
             "is_unsafe" => true,
             "is_variadic" => false,
             "inputs" => [ref(parent, "Mut")],
             "output" => unit()
           },
         true <-
           CallModels.expand(trait, refs) == %{"id" => trait["id"], "generics" => args([parent])},
         true <- forwarded_allocator?(inherited, var(count - 1), ctx),
         true <-
           CallModels.expand(inherited["types"], refs) == variables and inherited["regions"] == [] and
             inherited["const_generics"] == [] and length(inherited["trait_refs"]) == 1,
         %{"src" => "Destruct", "is_unsafe" => false, "is_negative" => false} = impl <-
           find(t["trait_impls"], impl_id),
         true <-
           impl["item_meta"]["name"] ==
             path(["alloc", "collections", "btree", family, type_name]) ++
               [%{"Impl" => %{"Trait" => impl_id}}],
         true <- params?(CallModels.expand(impl["generics"], refs), count, 0, 1),
         true <- clauses?(CallModels.expand(impl["generics"], refs), "len", false, count, ctx),
         true <-
           CallModels.expand(impl["impl_trait"], refs) == %{
             "id" => trait["id"],
             "generics" => args([parent])
           },
         true <- impl["types"] == [] and impl["consts"] == [] and impl["implied_trait_refs"] == [],
         [
           %{
             "kind" => %{"TraitMethod" => [trait_id, 0]},
             "params" => method_params,
             "skip_binder" => %{"id" => ^id, "generics" => forwarded}
           }
         ] <- impl["methods"],
         true <- trait_id == trait["id"] and params?(method_params, 0, 1, 0),
         true <- forwarded_allocator?(forwarded, var(count - 1), ctx),
         true <-
           CallModels.expand(forwarded["types"], refs) == variables and
             forwarded["regions"] == [%{"Var" => %{"Bound" => [0, 0]}}] and
             forwarded["const_generics"] == [] and length(forwarded["trait_refs"]) == 1 do
      entry = %{
        definition_id: id,
        rust_name: "alloc::collections::btree::#{family}::#{type_name}::drop_glue",
        type: type_name <> "<u64>/Global",
        self: self,
        first_party: false,
        status: :modelled,
        implementation_verified: false,
        ordered_collection: family,
        supported_drop_kinds: ["Precise", "Conditional"],
        dependencies: [],
        label:
          "Ordered collection Global deallocation model with scalar u64 keys/values: no user element destructor; conditional drop/skip is nonobservable in this pure model; allocator effects/failure and native drop implementation/deallocation correctness remain unverified"
      }

      {trait_id, id, entry}
    else
      _ ->
        raise ArgumentError,
              "unsupported or inconsistent ordered collection drop, scalar payload, allocator or compiler dictionary"
    end
  end

  defp forwarded_allocator?(g, allocator, ctx) do
    case g["trait_refs"] do
      [raw] ->
        case ResourceModels.dictionary(raw, ResourceModels.trait_references(ctx.t)) do
          %{
            "kind" => %{"Clause" => [%{"Free" => 0}, %{"regions" => []}]},
            "trait_decl_ref" => declared
          } ->
            CallModels.expand(declared, ctx.refs) == %{
              "id" => ctx.traits["AllocatorClone"],
              "generics" => args([allocator])
            }

          _ ->
            false
        end

      _ ->
        false
    end
  end

  defp unit, do: %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => args([])}}

  defp clauses?(p, "new", _, _, _), do: p["trait_clauses"] == []

  defp clauses?(p, method, function?, n, ctx) do
    clauses =
      cond do
        function? and method in ~w(get contains remove) ->
          [
            {"AllocatorClone", [var(n - 2)]},
            {"Borrow", [var(0), var(n - 1)]},
            {"Ord", [var(0)]},
            {"Ord", [var(n - 1)]}
          ]

        function? and method == "insert" ->
          [{"AllocatorClone", [var(n - 1)]}, {"Ord", [var(0)]}]

        true ->
          [{"AllocatorClone", [var(n - 1)]}]
      end

    Enum.map(p["trait_clauses"], fn clause ->
      if Map.take(clause["trait_"], ~w(regions outlives)) == %{"regions" => [], "outlives" => []},
        do: {clause["clause_id"], get_in(clause, ["trait_", "skip_binder"])},
        else: :unsupported_binder
    end) ==
      for {{name, types}, i} <- Enum.with_index(clauses),
          do:
            {i,
             %{
               "id" => ctx.traits[name],
               "generics" => args(types)
             }}
  end

  defp signature?(s, _family, "new", self, _, _), do: s["inputs"] == [] and s["output"] == self

  defp signature?(s, family, "insert", self, t, refs) do
    inputs =
      if family == "map", do: [ref(self, "Mut"), var(0), var(1)], else: [ref(self, "Mut"), var(0)]

    s["inputs"] == inputs and
      if(family == "map",
        do: option?(s["output"], var(1), t, refs),
        else: s["output"] == %{"Scalar" => "Bool"}
      )
  end

  defp signature?(s, family, method, self, t, refs) when method in ~w(get contains remove) do
    count = elem(@families[family], 1)
    mode = if method == "remove", do: "Mut", else: "Shared"
    input = %{"Ref" => [%{"Var" => %{"Free" => 1}}, var(count), "Shared"]}

    output? =
      if family == "map" do
        item = if method == "get", do: ref(var(1), "Shared"), else: var(1)
        option?(s["output"], item, t, refs)
      else
        s["output"] == %{"Scalar" => "Bool"}
      end

    s["inputs"] == [ref(self, mode), input] and output?
  end

  defp signature?(s, _, "len", self, _, _),
    do: s["inputs"] == [ref(self, "Shared")] and s["output"] == usize()

  defp option?(%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => g}}, item, t, refs),
    do: g == args([item]) and OptionModels.option_type?(find(t["type_decls"], id), refs)

  defp option?(_, _, _, _), do: false

  defp type?(
         %{
           "src" => "Normal",
           "kind" => "Opaque",
           "item_meta" => %{"name" => name},
           "generics" => p
         },
         family
       ) do
    {type, n} = @families[family]
    name == path(["alloc", "collections", "btree", family, type]) and params?(p, n, 0, 0)
  end

  defp type?(_, _), do: false

  defp global?(id, t) do
    match?(
      %{
        "src" => "Normal",
        "kind" => "Opaque",
        "item_meta" => %{
          "name" => [
            %{"Ident" => ["alloc", 0]},
            %{"Ident" => ["alloc", 0]},
            %{"Ident" => ["Global", 0]}
          ]
        }
      },
      find(t["type_decls"], id)
    ) and params?(find(t["type_decls"], id)["generics"], 0, 0, 0)
  end

  defp params?(p, n, r, c, query? \\ false)

  defp params?(p, n, r, c, query?) when is_map(p) do
    Enum.map(p["types"], & &1["index"]) == indices(n) and
      Enum.map(p["regions"], & &1["index"]) == indices(r) and
      p["const_generics"] == [] and p["trait_type_constraints"] == [] and
      length(p["trait_clauses"]) == c and
      p["outlives"] ==
        if(r == 0,
          do: [],
          else:
            Enum.map(
              indices(n),
              &%{
                "regions" => [],
                "outlives" => [],
                "skip_binder" => [
                  %{"Lub" => var(&1)},
                  %{"Var" => %{"Free" => if(query? and &1 == n - 1, do: 1, else: 0)}}
                ]
              }
            )
        )
  end

  defp params?(_, _, _, _, _), do: false

  defp local?(%{"item_meta" => %{"name" => [%{"Ident" => [name, 0]} | _]}}, crates),
    do: name in crates

  defp local?(_, _), do: false
  defp free(%{"TypeVar" => %{"Bound" => [depth, i]}}) when depth in [0, 1], do: var(i)
  defp free(m) when is_map(m), do: Map.new(m, fn {k, v} -> {k, free(v)} end)
  defp free(l) when is_list(l), do: Enum.map(l, &free/1)
  defp free(v), do: v
  defp indices(0), do: []
  defp indices(n), do: Enum.to_list(0..(n - 1))
  defp find(l, id), do: Enum.find(l || [], &(&1 && &1["def_id"] == id))
  defp args(types), do: ResourceModels.args(types)
  defp var(i), do: %{"TypeVar" => %{"Free" => i}}
  defp ref(type, kind), do: %{"Ref" => [%{"Var" => %{"Free" => 0}}, type, kind]}
  defp adt(id, types), do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args(types)}}
  defp u64, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}}
  defp usize, do: %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}
  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})
end
