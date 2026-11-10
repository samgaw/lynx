defmodule Lynx.Rust.ExplicitOwnership do
  @moduledoc false
  alias Lynx.Rust.{CallModels, DropModels, LLBC}

  @namespace "LynxCompilerOwnership"
  @arguments %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}
  @parameters %{
    "regions" => [],
    "types" => [],
    "const_generics" => [],
    "trait_clauses" => [],
    "outlives" => [],
    "trait_type_constraints" => []
  }

  # Preserve explicit compiler ownership dictionaries through Aeneas's marker
  # filtering. No application body is changed. The only synthesized operation
  # is the identity update justified by a compiler NoopDestruct closed-value witness.
  def prepare!(
        %{"charon_version" => "0.1.304", "has_errors" => false, "translated" => translated} =
          document
      ) do
    unless translated["options"]["precise_drops"] == true and
             translated["options"]["desugar_drops"] == true,
           do: reject!("precise and desugared drops are required")

    if contains_drop?(translated["fun_decls"]), do: reject!("unlowered drop statement")

    for section <- ~w(type_decls fun_decls trait_decls trait_impls global_decls),
        item <- translated[section] || [],
        item != nil,
        List.first(item["item_meta"]["name"]) == %{"Ident" => [@namespace, 0]},
        do: reject!("reserved compiler ownership namespace already exists")

    for section <- ~w(type_decls fun_decls trait_decls trait_impls global_decls),
        {item, index} <- Enum.with_index(translated[section] || []),
        item != nil and item["def_id"] != index,
        do: reject!("inconsistent declaration identity")

    Lynx.Rust.ResourceModels.trait_references(translated)
    refs = LLBC.type_references!(document)
    [destruct] = named!(translated["trait_decls"], ~w(core marker Destruct))
    id = destruct["def_id"]

    unless DropModels.standard_destruct_trait?(id, translated, refs),
      do: reject!("invalid compiler Destruct interface")

    {span, meta_span} = source_span!(translated["fun_decls"])

    state = %{
      trait: id,
      refs: refs,
      type_ids: MapSet.new(for type <- translated["type_decls"], type != nil, do: type["def_id"]),
      next_impl: length(translated["trait_impls"]),
      next_fun: length(translated["fun_decls"]),
      impls: [],
      instances: %{},
      function: nil,
      next_ref: max_ref(document) + 1,
      span: span,
      meta_span: meta_span
    }

    {document, state} = walk(document, state)
    translated = document["translated"]

    traits =
      Enum.map(translated["trait_decls"], fn
        nil ->
          nil

        trait ->
          case trait["item_meta"]["name"] do
            [
              %{"Ident" => ["core", 0]},
              %{"Ident" => ["marker", 0]},
              %{"Ident" => ["Destruct", 0]}
            ] ->
              put_in(trait, ["item_meta", "name"], path([@namespace, "Destruct"]))

            [
              %{"Ident" => ["core", 0]},
              %{"Ident" => ["ops", 0]},
              %{"Ident" => ["drop", 0]},
              %{"Ident" => ["Drop", 0]}
            ] ->
              put_in(trait, ["item_meta", "name"], path([@namespace, "Drop"]))

            _ ->
              trait
          end
      end)

    functions = translated["fun_decls"] ++ if(state.function, do: [state.function], else: [])

    adapted =
      translated
      |> Map.put("trait_decls", traits)
      |> Map.put("fun_decls", functions)
      |> Map.put("trait_impls", translated["trait_impls"] ++ Enum.reverse(state.impls))

    adapted = order_models(adapted, state)

    %{
      document: %{document | "translated" => adapted},
      renamed_traits:
        Enum.zip(translated["trait_decls"], traits)
        |> Enum.filter(fn {a, b} -> a != b end)
        |> Enum.map(fn {original, _} -> {original["def_id"], original["item_meta"]["name"]} end)
        |> Map.new(),
      primitive_models:
        Enum.map(state.instances, fn {type, impl} ->
          %{
            type: type,
            implementation_id: impl,
            function_id: state.next_fun,
            implementation_verified: false,
            label:
              "Compiler NoopDestruct closed-value primitive; identity borrow update, no destructor effects; compiler correctness trusted"
          }
        end)
    }
  end

  def prepare!(_), do: reject!("error-free pinned Charon input required")

  defp walk(
         %{
           "kind" => %{"BuiltinOrAuto" => %{"builtin_data" => "NoopDestruct"} = data},
           "trait_decl_ref" => declaration
         } = ref,
         state
       ) do
    args = CallModels.expand(declaration["generics"], state.refs)

    with true <- declaration["id"] == state.trait,
         true <-
           data == %{
             "builtin_data" => "NoopDestruct",
             "parent_trait_refs" => [],
             "types" => [],
             "vtable" => nil
           },
         %{"types" => [type]} <- args,
         true <- args == %{@arguments | "types" => [type]},
         true <- supported_noop_type?(type, state.type_ids) do
      [raw_self] = declaration["generics"]["types"]

      self =
        case raw_self do
          %{"Value" => [id, _]} -> %{"Deduplicated" => id}
          %{"Deduplicated" => _} = ref -> ref
          _ -> reject!("missing shared type identity for NoopDestruct")
        end

      {impl, state} = instance(type, self, state)
      {%{ref | "kind" => %{"TraitImpl" => %{"id" => impl, "generics" => @arguments}}}, state}
    else
      _ -> reject!("unsupported or inconsistent compiler NoopDestruct witness")
    end
  end

  defp walk(map, state) when is_map(map) do
    {entries, state} =
      Enum.map_reduce(map, state, fn {key, value}, state ->
        {value, state} = walk(value, state)
        {{key, value}, state}
      end)

    {Map.new(entries), state}
  end

  defp walk(list, state) when is_list(list), do: Enum.map_reduce(list, state, &walk/2)
  defp walk(value, state), do: {value, state}

  defp supported_noop_type?(type, ids) do
    DropModels.primitive_scalar?(type) or
      case type do
        %{
          "Adt" => %{
            "id" => id,
            "builtin" => builtin,
            "generics" => %{
              "regions" => [],
              "types" => types,
              "const_generics" => [],
              "trait_refs" => []
            }
          }
        } ->
          (MapSet.member?(ids, id) or builtin == "Tuple") and
            Enum.all?(types, &supported_noop_type?(&1, ids))

        _ ->
          false
      end
  end

  defp instance(type, self, state) do
    case state.instances do
      %{^type => id} ->
        {id, state}

      _ ->
        state = if state.function, do: state, else: %{state | function: noop_function(state)}
        id = state.next_impl
        # Keep the compiler's original self type identity. All original
        # declarations precede these appended intrinsic instances.
        impl = %{
          "def_id" => id,
          "item_meta" => meta(state.meta_span, "Noop#{id}"),
          "src" => "Normal",
          "impl_trait" => %{"id" => state.trait, "generics" => %{@arguments | "types" => [self]}},
          "is_negative" => false,
          "is_unsafe" => false,
          "generics" => @parameters,
          "implied_trait_refs" => [],
          "consts" => [],
          "types" => [],
          "methods" => [
            %{
              "params" => %{@parameters | "regions" => [region()]},
              "kind" => %{"TraitMethod" => [state.trait, 0]},
              "skip_binder" => %{
                "id" => state.next_fun,
                "generics" => %{
                  @arguments
                  | "regions" => [%{"Var" => %{"Bound" => [0, 0]}}],
                    "types" => [self]
                }
              }
            }
          ],
          "vtable" => "NotDynCompatible"
        }

        {id,
         %{
           state
           | next_impl: id + 1,
             impls: [impl | state.impls],
             instances: Map.put(state.instances, type, id)
         }}
    end
  end

  defp order_models(translated, %{function: nil}), do: translated

  defp order_models(translated, state) do
    models = MapSet.new(Enum.map(state.impls, & &1["def_id"]))

    sections = %{
      "Fun" => "fun_decls",
      "Type" => "type_decls",
      "Global" => "global_decls",
      "TraitDecl" => "trait_decls",
      "TraitImpl" => "trait_impls"
    }

    {ordered, remaining} =
      Enum.map_reduce(translated["ordered_decls"], models, fn group, remaining ->
        [{kind, ids}] = Map.to_list(group)

        ids =
          case ids do
            %{"NonRec" => id} -> [id]
            %{"Rec" => ids} -> ids
          end

        needed =
          Enum.reduce(ids, MapSet.new(), fn id, found ->
            declaration =
              Enum.find(translated[Map.fetch!(sections, kind)], &(&1 && &1["def_id"] == id))

            MapSet.union(found, model_references(declaration, models))
          end)
          |> MapSet.intersection(remaining)

        declarations = Enum.map(Enum.sort(needed), &%{"TraitImpl" => %{"NonRec" => &1}})
        {declarations ++ [group], MapSet.difference(remaining, needed)}
      end)

    groups =
      [%{"Fun" => %{"NonRec" => state.next_fun}}] ++
        List.flatten(ordered) ++
        Enum.map(Enum.sort(remaining), &%{"TraitImpl" => %{"NonRec" => &1}})

    Map.put(translated, "ordered_decls", groups)
  end

  defp model_references(%{"TraitImpl" => %{"id" => id}} = map, ids) do
    found = if MapSet.member?(ids, id), do: MapSet.new([id]), else: MapSet.new()
    Enum.reduce(Map.values(map), found, &MapSet.union(model_references(&1, ids), &2))
  end

  defp model_references(map, ids) when is_map(map),
    do: Enum.reduce(Map.values(map), MapSet.new(), &MapSet.union(model_references(&1, ids), &2))

  defp model_references(list, ids) when is_list(list),
    do: Enum.reduce(list, MapSet.new(), &MapSet.union(model_references(&1, ids), &2))

  defp model_references(_, _), do: MapSet.new()

  defp noop_function(state) do
    n = state.next_ref
    variable = %{"Value" => [n, %{"TypeVar" => %{"Free" => 0}}]}

    input = %{
      "Value" => [n + 1, %{"Ref" => [%{"Var" => %{"Free" => 0}}, %{"Deduplicated" => n}, "Mut"]}]
    }

    unit = %{
      "Value" => [n + 2, %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => @arguments}}]
    }

    ref = fn i -> %{"Deduplicated" => i} end
    body_input = %{"Value" => [n + 3, %{"Ref" => [%{"Body" => 1}, ref.(n), "Mut"]}]}

    local = fn index, type ->
      %{
        "index" => index,
        "name" => nil,
        "span" => state.span,
        "ty" => type,
        "drop_flag_for" => nil
      }
    end

    statement = fn id, kind ->
      %{"id" => id, "span" => state.span, "kind" => kind, "comments_before" => []}
    end

    %{
      "def_id" => state.next_fun,
      "item_meta" => meta(state.meta_span, "noop"),
      "src" => "Normal",
      "generics" => %{
        @parameters
        | "regions" => [region()],
          "types" => [%{"index" => 0, "name" => "T", "variance" => "Invariant"}],
          "outlives" => [
            %{
              "regions" => [],
              "outlives" => [],
              "skip_binder" => [%{"Lub" => variable}, %{"Var" => %{"Free" => 0}}]
            }
          ]
      },
      "signature" => %{
        "is_unsafe" => true,
        "is_variadic" => false,
        "abi" => "Rust",
        "inputs" => [input],
        "output" => unit
      },
      "body" => %{
        "Structured" => %{
          "span" => state.span,
          "bound_body_regions" => 2,
          "comments" => [],
          "locals" => %{
            "arg_count" => 1,
            "locals" => [local.(0, ref.(n + 2)), local.(1, body_input)]
          },
          "body" => %{
            "id" => 0,
            "span" => state.span,
            "statements" => [
              statement.(0, %{"StorageLive" => 0}),
              statement.(1, %{
                "Assign" => [
                  %{"kind" => %{"Local" => 0}, "ty" => ref.(n + 2)},
                  %{
                    "Aggregate" => [
                      %{
                        "Adt" => [
                          %{"id" => 0, "builtin" => "Tuple", "generics" => @arguments},
                          nil,
                          nil
                        ]
                      },
                      []
                    ]
                  }
                ]
              }),
              statement.(2, "Return")
            ]
          }
        }
      }
    }
  end

  defp meta(span, name),
    do: %{
      "name" => path([@namespace, name]),
      "span" => span,
      "source_text" => nil,
      "attr_info" => %{"attributes" => [], "inline" => nil, "rename" => nil, "public" => true},
      "is_local" => false,
      "started_from" => false,
      "is_extern" => false,
      "opacity" => "Transparent",
      "lang_item" => nil,
      "diagnostic_item" => nil,
      "has_errors" => false
    }

  defp region,
    do: %{
      "index" => 0,
      "name" => nil,
      "variance" => "Covariant",
      "mutability" => "Unknown",
      "late_bound" => true
    }

  defp path(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  defp named!(items, parts) do
    matches = Enum.filter(items, &(&1 && &1["item_meta"]["name"] == path(parts)))
    unless length(matches) == 1, do: reject!("missing or duplicate compiler Destruct trait")
    matches
  end

  defp source_span!(functions) do
    first = Enum.find(functions, &(&1 && is_map(&1["body"])))

    case first && first["body"]["Structured"]["span"] do
      %{"Value" => [id, _]} -> {%{"Deduplicated" => id}, first["item_meta"]["span"]}
      %{"Deduplicated" => _} = span -> {span, first["item_meta"]["span"]}
      _ -> reject!("missing source span")
    end
  end

  defp contains_drop?(%{"Drop" => _}), do: true
  defp contains_drop?(map) when is_map(map), do: Enum.any?(Map.values(map), &contains_drop?/1)
  defp contains_drop?(list) when is_list(list), do: Enum.any?(list, &contains_drop?/1)
  defp contains_drop?(_), do: false
  defp max_ref(%{"Value" => [id, value]}) when is_integer(id), do: max(id, max_ref(value))
  defp max_ref(map) when is_map(map), do: Enum.reduce(Map.values(map), 0, &max(max_ref(&1), &2))
  defp max_ref(list) when is_list(list), do: Enum.reduce(list, 0, &max(max_ref(&1), &2))
  defp max_ref(_), do: 0
  defp reject!(message), do: raise(ArgumentError, "explicit Rust ownership: " <> message)
end
