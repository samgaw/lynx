defmodule Lynx.Rustler.Registrations do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Extraction, Fingerprint, LLBC, NativeCodecs, ResourceModels}
  @registration ~w(rustler resource registration Registration)

  def prepare!(extraction, context, tools, expanded, compiled, project, prefix) do
    if Enum.any?(extraction.audit.external_calls, fn {_, m} -> m[:native_resource_type] end) do
      crate = context.artifact["target"]["name"]
      metadata = Lynx.Rustler.Metadata.resources!(expanded, compiled, crate)
      modules = metadata["registrations"] |> Enum.map(& &1["modules"]) |> Enum.uniq()

      roots =
        [crate <> "::" <> metadata["loader"]] ++
          for(
            module <- modules,
            name <- ~w(__INVENTORY __ctor __CTOR),
            do: Enum.join([crate | module] ++ ["_", name], "::")
          )

      raw =
        Extraction.describe!(context, tools, roots, project, prefix <> ".ResourceRegistration",
          # Inventory roots can also select NIF records in anonymous constants.
          # Their raw FFI entry bodies are irrelevant to registration metadata.
          # Actual selected NIF computations were extracted and audited above.
          opaque_functions: [crate <> "::_::__INVENTORY::nif_func"]
        )

      entries = resolve!(metadata, raw.document, crate)
      required = required_types!(extraction)

      selected =
        Enum.map(required, fn type ->
          case Enum.filter(entries, &(&1.rust_name == type.rust_name)) do
            [registration] ->
              Map.merge(registration, type)

            _ ->
              raise ArgumentError,
                    "missing or ambiguous compiled resource registration for #{type.rust_name}"
          end
        end)

      %{
        types: selected,
        inventory: entries,
        compiler_file: raw.llbc,
        metadata: metadata,
        status: :validated_configuration,
        fingerprint:
          Fingerprint.digest(
            :erlang.term_to_binary({metadata, Fingerprint.file!(raw.llbc), selected}, [
              :deterministic
            ])
          ),
        boundary:
          "Rustler 0.39 generated loader/inventory configuration checked against compiler-resolved identities and compiled load-callback presence; successful library loading, linker constructors, registration execution and FFI remain trusted"
      }
    else
      %{types: [], inventory: [], status: :not_required, fingerprint: nil, boundary: nil}
    end
  end

  def resolve!(metadata, document, crate) do
    t = document["translated"]
    refs = LLBC.type_references!(document)
    functions = Map.new(Enum.reject(t["fun_decls"], &is_nil/1), &{&1["def_id"], &1})
    globals = Enum.reject(t["global_decls"], &is_nil/1)
    loader_name = path([crate, metadata["loader"], "nif_load"])
    [loader] = Enum.filter(Map.values(functions), &(&1["item_meta"]["name"] == loader_name))

    unless Enum.any?(calls(loader["body"]), fn {id, _} ->
             inherent?(functions[id], "register_all_collected", @registration, t, refs)
           end),
           do:
             raise(
               ArgumentError,
               "resource loader does not call the actual Rustler registration implementation"
             )

    entries =
      Enum.flat_map(Enum.group_by(metadata["registrations"], & &1["modules"]), fn {modules,
                                                                                   expected} ->
        if Enum.any?(expected, &(&1["name"] != nil)),
          do: raise(ArgumentError, "named resource registration is not yet supported")

        prefix = path([crate | modules])

        nodes =
          Enum.filter(globals, fn g ->
            case g["item_meta"]["name"] do
              name when length(name) == length(prefix) + 2 ->
                Enum.take(name, length(prefix)) == prefix and
                  Enum.any?(
                    expected,
                    &(Enum.at(name, -2) == %{"Ident" => ["_", &1["anonymous_index"]]})
                  ) and
                  List.last(name) == %{"Ident" => ["__INVENTORY", 0]}

              _ ->
                false
            end
          end)

        found =
          Enum.flat_map(nodes, fn node ->
            closure = initializer_closure(node, globals, functions, [])

            constructors =
              for f <- closure,
                  {id, args} <- calls(f["body"]),
                  inherent?(functions[id], "new", @registration, t, refs),
                  do: {functions[id], args}

            case constructors do
              [] ->
                []

              [{f, args}] ->
                unless nominal?(node["ty"], ~w(inventory Node), t, refs),
                  do:
                    raise(
                      ArgumentError,
                      "resource inventory node has an inconsistent compiler type"
                    )

                parent = Enum.drop(node["item_meta"]["name"], -1)

                [ctor] =
                  Enum.filter(
                    Map.values(functions),
                    &(&1["item_meta"]["name"] == parent ++ path(["__ctor"]))
                  )

                unless submits?(ctor["body"], t) and
                         node["def_id"] in global_ids(ctor["body"]),
                       do:
                         raise(
                           ArgumentError,
                           "resource constructor does not submit its actual inventory node"
                         )

                %{
                  "types" => [payload],
                  "regions" => [],
                  "const_generics" => [],
                  "trait_refs" => [_]
                } = args

                payload = CallModels.expand(payload, refs)
                %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => empty}} = payload

                unless empty == ResourceModels.args([]) and f["signature"]["inputs"] == [],
                  do:
                    raise(
                      ArgumentError,
                      "resource registration requires a concrete monomorphic type"
                    )

                params = CallModels.expand(f["generics"], refs)
                [clause] = params["trait_clauses"]
                resource_trait = clause["trait_"]["skip_binder"]["id"]

                unless ResourceModels.params?(params, 0, [clause]) and
                         ResourceModels.resource_clause?(clause, resource_trait, refs) and
                         Enum.any?(
                           t["trait_decls"],
                           &(&1 && &1["def_id"] == resource_trait &&
                               &1["item_meta"]["name"] ==
                                 path(~w(rustler resource traits Resource)))
                         ) and
                         nominal?(f["signature"]["output"], @registration, t, refs),
                       do:
                         raise(
                           ArgumentError,
                           "inconsistent compiler Resource registration signature"
                         )

                [type] = Enum.filter(t["type_decls"], &(&1 && &1["def_id"] == id))

                [
                  %{
                    rust_name: nominal_name!(type),
                    modules: modules,
                    source: node["item_meta"]["span"]
                  }
                ]

              _ ->
                raise ArgumentError, "ambiguous resource inventory constructor"
            end
          end)

        unless length(found) == length(expected),
          do:
            raise(
              ArgumentError,
              "expanded resource inventory does not match compiler-resolved registrations"
            )

        found
      end)

    unless length(entries) == MapSet.size(MapSet.new(entries, & &1.rust_name)),
      do: raise(ArgumentError, "duplicate resource registration")

    entries
  rescue
    e in [MatchError, KeyError, FunctionClauseError] ->
      raise ArgumentError,
            "missing or inconsistent compiler resource registration: #{Exception.message(e)}"
  end

  defp initializer_closure(node, globals, functions, seen) do
    if node["def_id"] in seen,
      do: raise(ArgumentError, "cyclic resource inventory initialization")

    f =
      case Enum.filter(
             Map.values(functions),
             &(is_map(&1["src"]) and
                 get_in(&1, ["src", "GlobalInitializer", "id"]) == node["def_id"])
           ) do
        [f] ->
          f

        _ ->
          raise ArgumentError,
                "missing resource inventory initializer #{inspect(node["item_meta"]["name"])}"
      end

    unless match?(%{"Structured" => _}, f["body"]),
      do: raise(ArgumentError, "missing resource initializer implementation")

    name = node["item_meta"]["name"] |> Enum.take_while(&(not is_map_key(&1, "Builtin")))

    children =
      Enum.filter(globals, fn g ->
        g["def_id"] in global_ids(f["body"]) and
          Enum.take(g["item_meta"]["name"], length(name)) == name
      end)

    [
      f
      | Enum.flat_map(
          children,
          &initializer_closure(&1, globals, functions, [node["def_id"] | seen])
        )
    ]
  end

  defp required_types!(extraction) do
    audit = extraction.audit

    ids =
      Enum.flat_map(audit.functions, fn f ->
        for {id, %{"types" => [payload]}} <- calls(f["body"]),
            audit.external_calls[id][:resource_operation] in ~w(new clone deref),
            %{"Adt" => %{"id" => type}} <- [CallModels.expand(payload, audit.references)],
            do: type
      end)
      |> Enum.uniq()

    # A checked consuming ResourceArc call also establishes its concrete payload.
    # Do not infer registration requirements from signature names alone.
    traits = ResourceModels.trait_references(audit.translated)

    dropped =
      for f <- audit.functions,
          {id, args} <- calls(f["body"]),
          audit.external_calls[id][:native_dispose] == true,
          Lynx.Rust.ResourceDrops.call?(
            args,
            audit.translated,
            audit.references,
            traits
          ),
          [self] = args["types"],
          %{"Adt" => %{"generics" => %{"types" => [payload]}}} =
            CallModels.expand(self, audit.references),
          %{"Adt" => %{"id" => type}} <- [CallModels.expand(payload, audit.references)],
          do: type

    ids = Enum.uniq(ids ++ dropped)

    plan = NativeCodecs.plan!(audit)

    Enum.map(ids, fn id ->
      [type] = Enum.filter(plan, &(&1["def_id"] == id))
      [binding] = Enum.filter(extraction.translation["types"], &(&1["def_id"] == id))

      unless binding["rust_name"] == nominal_name!(type),
        do: raise(ArgumentError, "resource type/codec correspondence mismatch")

      %{
        rust_name: binding["rust_name"],
        lean_name: binding["lean_name"],
        tag: "resource<" <> type.native_tag <> ">"
      }
    end)
  end

  defp submits?(body, translated) do
    refs = ResourceModels.trait_references(translated)

    Enum.any?(regulars(body), fn
      %{"kind" => %{"Trait" => [dictionary, 0]}} ->
        case ResourceModels.dictionary(
               %{"regions" => [], "outlives" => [], "skip_binder" => dictionary},
               refs
             ) do
          %{"kind" => "Dyn", "trait_decl_ref" => %{"id" => id}} ->
            Enum.any?(
              translated["trait_decls"],
              &(&1 && &1["def_id"] == id &&
                  &1["item_meta"]["name"] == path(~w(inventory ErasedNode)))
            ) and
              Enum.at(translated["assoc_item_names"], id)["methods"] == ["submit"]

          _ ->
            false
        end

      _ ->
        false
    end)
  end

  defp regulars(%{"Regular" => pointer}), do: [pointer]
  defp regulars(map) when is_map(map), do: Enum.flat_map(Map.values(map), &regulars/1)
  defp regulars(list) when is_list(list), do: Enum.flat_map(list, &regulars/1)
  defp regulars(_), do: []

  defp inherent?(nil, _, _, _, _), do: false

  defp inherent?(f, method, nominal, t, refs) do
    case f["item_meta"]["name"] do
      name when length(name) == length(nominal) + 1 ->
        {namespace, [_]} = Enum.split(nominal, -1)
        prefix = path(namespace)

        case Enum.drop(name, length(prefix)) do
          [
            %{"Impl" => %{"Ty" => %{"kind" => "InherentImplBlock", "skip_binder" => parent}}},
            %{"Ident" => [^method, 0]}
          ] ->
            Enum.take(name, length(prefix)) == prefix and f["body"] == "Opaque" and
              f["src"] == "Normal" and nominal?(parent, nominal, t, refs) and
              match?(
                %{"abi" => "Rust", "is_unsafe" => false, "is_variadic" => false},
                f["signature"]
              )

          _ ->
            false
        end

      _ ->
        false
    end
  end

  defp nominal?(ty, name, t, refs) do
    case CallModels.expand(ty, refs) do
      %{"Adt" => %{"id" => id, "builtin" => nil}} ->
        Enum.any?(
          t["type_decls"],
          &(&1 && &1["def_id"] == id && &1["item_meta"]["name"] == path(name))
        )

      _ ->
        false
    end
  end

  defp nominal_name!(type),
    do: Enum.map_join(type["item_meta"]["name"], "::", fn %{"Ident" => [name, 0]} -> name end)

  defp calls(%{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => args}}), do: [{id, args}]
  defp calls(map) when is_map(map), do: Enum.flat_map(Map.values(map), &calls/1)
  defp calls(list) when is_list(list), do: Enum.flat_map(list, &calls/1)
  defp calls(_), do: []
  defp global_ids(%{"Global" => %{"id" => id}}), do: [id]
  defp global_ids(map) when is_map(map), do: Enum.flat_map(Map.values(map), &global_ids/1)
  defp global_ids(list) when is_list(list), do: Enum.flat_map(list, &global_ids/1)
  defp global_ids(_), do: []
  defp path(names), do: Enum.map(names, &%{"Ident" => [&1, 0]})
end
