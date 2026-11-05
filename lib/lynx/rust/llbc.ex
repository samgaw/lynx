defmodule Lynx.Rust.LLBC do
  @moduledoc false

  @library_kinds ~w(lib rlib dylib cdylib staticlib)
  @standard_crates ~w(core alloc std proc_macro test)

  def crate_names!(workspace) do
    names =
      for crate <- workspace.crates,
          target <- crate.targets,
          Enum.any?(target["kind"], &(&1 in @library_kinds)),
          do: target["name"]

    if length(names) != MapSet.size(MapSet.new(names)),
      do: raise(ArgumentError, "ambiguous first-party Rust crate identities")

    members = MapSet.new(Enum.map(workspace.crates, & &1.id))

    foreign_names =
      for {id, package} <- workspace.packages,
          not MapSet.member?(members, id),
          target <- package["targets"],
          Enum.any?(target["kind"], &(&1 in @library_kinds)),
          do: target["name"]

    if Enum.any?(foreign_names, &(&1 in @standard_crates)) or
         Enum.any?(names, &(&1 in @standard_crates or &1 in foreign_names)),
       do:
         raise(
           ArgumentError,
           "ambiguous Rust crate name shared with a standard or external crate"
         )

    names
  end

  def audit!(document, first_party, opts \\ []) do
    unless match?(
             %{
               "charon_version" => "0.1.304",
               "has_errors" => false,
               "translated" => %{"fun_decls" => _, "type_decls" => _}
             },
             document
           ),
           do:
             raise(
               ArgumentError,
               "incomplete LLBC or unsupported Charon version (expected 0.1.304)"
             )

    translated = document["translated"]

    {functions, external} =
      translated["fun_decls"]
      |> Enum.reject(&is_nil/1)
      |> Enum.split_with(&first_party?(&1, first_party))

    if functions == [],
      do: raise(ArgumentError, "no first-party function implementations were extracted")

    {library_helpers, external} =
      Enum.split_with(external, &Lynx.Rust.LibraryHelpers.selected?(&1, translated))

    functions = functions ++ library_helpers

    all_functions = functions
    ids = Enum.map(all_functions, & &1["def_id"])

    if length(ids) != MapSet.size(MapSet.new(ids)),
      do: raise(ArgumentError, "duplicate LLBC function identity")

    refs = references(document, %{})

    {generated_drops, functions} = Enum.split_with(functions, &Lynx.Rust.DropModels.generated?/1)

    {initializers, ordinary} =
      Enum.split_with(
        functions,
        &(is_map(&1["src"]) && Map.has_key?(&1["src"], "GlobalInitializer"))
      )

    globals =
      Enum.filter(translated["global_decls"], &(&1 != nil && first_party?(&1, first_party)))

    constants = Lynx.Rust.Constants.audit!(globals, initializers, refs, translated["type_decls"])

    available_models =
      Lynx.Rust.CallModels.resolve(
        external,
        translated,
        refs,
        Keyword.get(opts, :external_calls, [])
      )

    direct_calls = Enum.flat_map(functions, &calls(&1["body"]))
    modelled = Map.take(available_models, direct_calls)

    callback_dependencies =
      case Lynx.Rust.ResultModels.audit(functions, modelled, translated, refs) do
        {:ok, dependencies} -> dependencies
        {:error, function, message} -> failure!(function, translated, message)
      end

    callback_ids = callback_dependencies |> Map.values() |> List.flatten() |> MapSet.new()

    trait_dependencies =
      case Lynx.Rust.FormatModels.audit(functions, available_models, translated, refs) do
        {:ok, dependencies} -> dependencies
        {:error, function, message} -> failure!(function, translated, message)
      end

    modelled =
      Map.take(
        available_models,
        direct_calls ++ (trait_dependencies |> Map.values() |> List.flatten())
      )

    allowed = %{
      functions: MapSet.new(Enum.map(functions, & &1["def_id"]) ++ Map.keys(modelled)),
      constants: constants
    }

    for function <- functions do
      unless match?(
               %{
                 "body" => %{"Structured" => _},
                 "item_meta" => %{"opacity" => "Transparent"},
                 "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"}
               },
               function
             ) or
               (MapSet.member?(callback_ids, function["def_id"]) and
                  match?(
                    %{
                      "body" => %{"Structured" => _},
                      "item_meta" => %{"opacity" => "Transparent"}
                    },
                    function
                  )) do
        failure!(function, translated, "missing or unsupported first-party implementation")
      end

      check_calls!(function["body"], allowed, function, translated)
    end

    # Preserve direct-call diagnostics before examining cleanup reached by those
    # calls. No extraction can proceed until the separate drop audit succeeds.
    drops =
      case Lynx.Rust.DropModels.audit(functions, generated_drops, translated, refs, first_party) do
        {:ok, drops} -> drops
        {:error, function, message} -> failure!(function, translated, message)
      end

    for type <- translated["type_decls"], type != nil, first_party?(type, first_party) do
      unless is_map(type["kind"]) &&
               Enum.any?(~w(Struct Enum Alias), &Map.has_key?(type["kind"], &1)),
             do: failure!(type, translated, "missing or unsupported first-party type definition")
    end

    dispatch_dependencies =
      Map.merge(callback_dependencies, trait_dependencies, fn _id, callbacks, methods ->
        Enum.uniq(callbacks ++ methods)
      end)

    check_constant_cycles!(functions, constants, translated, dispatch_dependencies)

    %{
      functions: ordinary,
      library_helpers: Enum.map(library_helpers, & &1["def_id"]),
      constant_initializers: initializers,
      callback_dependencies: callback_dependencies,
      trait_dependencies: trait_dependencies,
      drops: drops,
      constants: constants,
      external_functions: external,
      external_calls: modelled,
      crate: translated["crate_name"],
      references: refs,
      translated: translated
    }
  end

  def link!(audit, translation) do
    unless translation["charon_version"] == "0.1.304" && translation["crate"] == audit.crate &&
             translation["aeneas_version"] in [
               "nightly-2026.11.04-2b9e3ea",
               "nightly-2026.11.04-2b9e3ea+lynx-static-loans-v1"
             ],
           do: raise(ArgumentError, "Aeneas translation does not match the LLBC crate/version")

    for id <- Map.keys(audit.external_calls),
        Enum.any?(translation["functions"], &(&1["def_id"] == id)),
        do:
          raise(
            ArgumentError,
            "external Rust call model was not applied by Aeneas (function #{id})"
          )

    Lynx.Rust.Constants.link!(audit.constants, translation)
    Lynx.Rust.DropModels.link!(audit.drops, translation)

    linked =
      for function <- audit.functions, into: %{} do
        matches = Enum.filter(translation["functions"], &(&1["def_id"] == function["def_id"]))

        case matches do
          [%{"is_opaque" => false, "lean_name" => name} = mapping] when is_binary(name) ->
            {function["def_id"], Map.put(mapping, "declaration", function)}

          _ ->
            failure!(
              function,
              audit.translated,
              "missing, ambiguous or opaque Aeneas implementation"
            )
        end
      end

    names = Enum.map(Map.values(linked), & &1["lean_name"])

    if length(names) != MapSet.size(MapSet.new(names)),
      do: raise(ArgumentError, "different Rust bodies map to the same Lean implementation")

    linked
  end

  def dependencies(audit) do
    Map.new(audit.functions ++ Map.get(audit, :constant_initializers, []), fn function ->
      initializer_calls =
        for id <- global_ids(function["body"]),
            global = Map.fetch!(audit.constants, id),
            initializer = Lynx.Rust.Constants.initializer_id(global),
            initializer != nil,
            do: initializer

      {function["def_id"],
       (calls(function["body"]) ++
          initializer_calls ++
          Map.get(Map.get(audit, :callback_dependencies, %{}), function["def_id"], []) ++
          Map.get(Map.get(audit, :trait_dependencies, %{}), function["def_id"], []))
       |> Enum.uniq()
       |> Enum.sort()}
    end)
  end

  defp global_ids(%{"Global" => %{"id" => id}}), do: [id]
  defp global_ids(value) when is_map(value), do: Enum.flat_map(Map.values(value), &global_ids/1)
  defp global_ids(value) when is_list(value), do: Enum.flat_map(value, &global_ids/1)
  defp global_ids(_), do: []

  defp check_constant_cycles!(_functions, constants, _translated, _callbacks)
       when map_size(constants) == 0,
       do: :ok

  defp check_constant_cycles!(functions, constants, translated, callbacks) do
    graph = :digraph.new()

    try do
      ids = MapSet.new(functions, & &1["def_id"])
      for id <- ids, do: :digraph.add_vertex(graph, {:function, id})
      for id <- Map.keys(constants), do: :digraph.add_vertex(graph, {:constant, id})

      for {id, global} <- constants,
          initializer = Lynx.Rust.Constants.initializer_id(global),
          initializer != nil,
          do: :digraph.add_edge(graph, {:constant, id}, {:function, initializer})

      for function <- functions do
        for id <- calls(function["body"]) ++ Map.get(callbacks, function["def_id"], []),
            MapSet.member?(ids, id),
            do: :digraph.add_edge(graph, {:function, function["def_id"]}, {:function, id})

        for id <- global_ids(function["body"]),
            do: :digraph.add_edge(graph, {:function, function["def_id"]}, {:constant, id})
      end

      for component <- :digraph_utils.strong_components(graph),
          length(component) > 1,
          {:constant, id} <- component do
        failure!(
          Map.fetch!(constants, id),
          translated,
          "cyclic Rust constant dependencies are unsupported"
        )
      end
    after
      :digraph.delete(graph)
    end
  end

  defp calls(
         %{"Call" => %{"call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => id}}}}}} = node
       ) do
    [id | Enum.flat_map(Map.values(node), &calls/1)]
  end

  defp calls(node) when is_map(node), do: Enum.flat_map(Map.values(node), &calls/1)
  defp calls(nodes) when is_list(nodes), do: Enum.flat_map(nodes, &calls/1)
  defp calls(_), do: []

  def signature!(function, audit) do
    signature = function["signature"]

    {Enum.map(signature["inputs"], &signature_type!(&1, audit)),
     signature_type!(signature["output"], audit)}
  end

  defp first_party?(%{"item_meta" => %{"name" => [%{"Ident" => [crate, _]} | _]}}, first_party),
    do: crate in first_party

  defp first_party?(_, _), do: false

  # Calls require first-party bodies or closed, explicitly audited models. Charon can emit
  # unused standard-library declarations; those are distinct from a call that
  # would actually rely on an unverified external model. Destructors are also
  # rejected unless the structural-erasure audit justifies Aeneas ownership removal.
  defp check_calls!(%{"Call" => call} = node, ids, function, translated) do
    case get_in(call, ["call", "func"]) do
      %{"Regular" => %{"kind" => %{"Fun" => id}}} ->
        unless MapSet.member?(ids.functions, id),
          do:
            failure!(
              function,
              translated,
              "unverified external Rust call #{callee_label(id, translated)} (function #{id})"
            )

      _ ->
        failure!(function, translated, "unsupported indirect Rust call")
    end

    Enum.each(Map.values(node), &check_calls!(&1, ids, function, translated))
  end

  defp check_calls!(%{"Assign" => [place, value]}, allowed, function, translated) do
    if contains_global?(place),
      do: failure!(function, translated, "Rust constant mutation is unsupported")

    check_calls!(value, allowed, function, translated)
  end

  defp check_calls!(
         %{"Ref" => %{"place" => place, "kind" => kind}} = node,
         allowed,
         function,
         translated
       ) do
    if kind != "Shared" and contains_global?(place),
      do: failure!(function, translated, "mutable Rust constant borrows are unsupported")

    Enum.each(Map.values(node), &check_calls!(&1, allowed, function, translated))
  end

  defp check_calls!(%{"Drop" => _drop} = node, allowed, function, translated) do
    Enum.each(Map.values(node), &check_calls!(&1, allowed, function, translated))
  end

  defp check_calls!(
         %{"Global" => %{"id" => id, "generics" => generics}},
         allowed,
         function,
         translated
       ) do
    unless Map.has_key?(allowed.constants, id) and Lynx.Rust.Constants.empty_arguments?(generics),
      do: failure!(function, translated, "missing or unsupported Rust constant reference #{id}")
  end

  defp check_calls!(%{"Global" => _}, _, function, translated),
    do: failure!(function, translated, "missing or unsupported Rust constant reference")

  defp check_calls!(node, ids, function, translated) when is_map(node),
    do: Enum.each(Map.values(node), &check_calls!(&1, ids, function, translated))

  defp check_calls!(nodes, ids, function, translated) when is_list(nodes),
    do: Enum.each(nodes, &check_calls!(&1, ids, function, translated))

  defp check_calls!(_, _, _, _), do: :ok

  defp contains_global?(%{"Global" => _}), do: true

  defp contains_global?(value) when is_map(value),
    do: Enum.any?(Map.values(value), &contains_global?/1)

  defp contains_global?(value) when is_list(value), do: Enum.any?(value, &contains_global?/1)
  defp contains_global?(_), do: false

  defp callee_label(id, translated) do
    case Enum.find(translated["fun_decls"], &(&1 != nil and &1["def_id"] == id)) do
      nil ->
        "<missing declaration>"

      callee ->
        Enum.map_join(callee["item_meta"]["name"], "::", fn
          %{"Ident" => [name, _]} -> name
          %{"Impl" => _} -> "{impl}"
          other -> inspect(other)
        end)
    end
  end

  # Charon uses separate hash-cons tables for types, trait references, etc.
  # Recognize Ty variants only; IDs in other families must not overwrite these.
  defp references(%{"Value" => [id, value]}, refs)
       when is_integer(id) and is_map(value) and
              (is_map_key(value, "Scalar") or is_map_key(value, "Adt") or
                 is_map_key(value, "TypeVar") or is_map_key(value, "Ref") or
                 is_map_key(value, "Slice") or is_map_key(value, "Array")) do
    case Map.fetch(refs, id) do
      {:ok, existing} when existing != value ->
        raise ArgumentError, "inconsistent LLBC shared type identity"

      _ ->
        references(value, Map.put(refs, id, value))
    end
  end

  defp references(map, refs) when is_map(map),
    do: Enum.reduce(Map.values(map), refs, &references/2)

  defp references(list, refs) when is_list(list), do: Enum.reduce(list, refs, &references/2)
  defp references(_, refs), do: refs

  defp signature_type!(%{"Value" => [_, value]}, audit), do: signature_type!(value, audit)

  defp signature_type!(%{"Deduplicated" => id}, audit),
    do: signature_type!(Map.fetch!(audit.references, id), audit)

  defp signature_type!(%{"Scalar" => "Bool"}, _), do: "bool"

  defp signature_type!(%{"Scalar" => %{"Integer" => %{"Signed" => width}}}, _)
       when width in ~w(I8 I16 I32 I64),
       do: String.downcase(width)

  defp signature_type!(%{"Scalar" => %{"Integer" => %{"Unsigned" => width}}}, _)
       when width in ~w(U8 U16 U32 U64),
       do: String.downcase(width)

  defp signature_type!(
         %{
           "Adt" => %{
             "id" => id,
             "builtin" => nil,
             "generics" => %{
               "types" => [],
               "regions" => [_],
               "const_generics" => [],
               "trait_refs" => []
             }
           }
         },
         audit
       ) do
    declaration = Enum.find(audit.translated["type_decls"], &(&1 && &1["def_id"] == id))
    models = Map.get(audit, :external_types, [])

    case declaration do
      %{
        "kind" => "Opaque",
        "item_meta" => %{
          "name" => [
            %{"Ident" => ["rustler", 0]},
            %{"Ident" => ["types", 0]},
            %{"Ident" => ["binary", 0]},
            %{"Ident" => ["Binary", 0]}
          ]
        }
      } ->
        if Enum.any?(
             models,
             &(&1.rust == "rustler::types::binary::Binary" and &1.lean == "Lynx.Rustler.Binary")
           ),
           do: "binary",
           else: raise(ArgumentError, "Rustler Binary requires its explicit FFI type model")

      _ ->
        raise ArgumentError, "unsupported lifetime-bearing NIF type in extracted signature"
    end
  end

  defp signature_type!(
         %{
           "Adt" => %{
             "id" => id,
             "builtin" => builtin,
             "generics" => %{
               "types" => types,
               "regions" => [],
               "const_generics" => [],
               "trait_refs" => []
             }
           }
         },
         audit
       ) do
    cond do
      builtin == "Tuple" and length(types) <= 7 ->
        %{"tuple" => Enum.map(types, &signature_type!(&1, audit))}

      builtin == nil and length(types) == 2 and result_type?(id, audit) ->
        %{"result" => Enum.map(types, &signature_type!(&1, audit))}

      true ->
        raise ArgumentError, "unsupported NIF ADT identity or tuple arity in extracted signature"
    end
  end

  defp signature_type!(type, _),
    do: raise(ArgumentError, "unsupported NIF type in extracted signature: #{inspect(type)}")

  def result_type?(id, audit) do
    case Enum.find(audit.translated["type_decls"], &(&1 && &1["def_id"] == id)) do
      %{
        "item_meta" => %{
          "name" => [
            %{"Ident" => ["core", 0]},
            %{"Ident" => ["result", 0]},
            %{"Ident" => ["Result", 0]}
          ]
        },
        "generics" => %{
          "regions" => [],
          "types" => [%{"index" => 0}, %{"index" => 1}],
          "const_generics" => [],
          "trait_clauses" => [],
          "outlives" => [],
          "trait_type_constraints" => []
        },
        "kind" => %{
          "Enum" => [
            %{
              "id" => 0,
              "name" => "Ok",
              "fields" => [%{"ty" => ok}],
              "discriminant" => %{"Signed" => ["Isize", "0"]}
            },
            %{
              "id" => 1,
              "name" => "Err",
              "fields" => [%{"ty" => err}],
              "discriminant" => %{"Signed" => ["Isize", "1"]}
            }
          ]
        }
      } ->
        unshare_type(ok, audit.references) == %{"TypeVar" => %{"Free" => 0}} and
          unshare_type(err, audit.references) == %{"TypeVar" => %{"Free" => 1}}

      _ ->
        false
    end
  end

  defp unshare_type(%{"Value" => [_, value]}, refs), do: unshare_type(value, refs)
  defp unshare_type(%{"Deduplicated" => id}, refs), do: unshare_type(Map.fetch!(refs, id), refs)
  defp unshare_type(value, _), do: value

  defp failure!(item, translated, message) do
    meta = item["item_meta"]
    span = get_in(meta, ["span", "Untagged", "data"]) || get_in(meta, ["span", "data"]) || %{}
    file = Enum.find(translated["files"], &(&1["id"] == span["file_id"]))
    name = if file, do: file["name"] |> Map.values() |> List.first(), else: "native"

    raise CompileError,
      file: name,
      line: get_in(span, ["beg", "line"]),
      description: "#{message}: #{inspect(meta["name"])}"
  end
end
