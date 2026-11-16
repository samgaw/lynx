defmodule Lynx.Rust.AllocatorLayout do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC}

  @vec Enum.map(~w(alloc vec Vec), &%{"Ident" => [&1, 0]})
  @global Enum.map(~w(alloc alloc Global), &%{"Ident" => [&1, 0]})

  # A nested generic drop loses its allocator dictionary under hide_allocator.
  # Recover evidence from the same compiler invocation with that pass disabled,
  # never from a Vec's erased representation or another value's destructor.
  def required?(document) do
    context = context(document, false)

    any?(document["translated"]["fun_decls"], fn
      %{"Drop" => %{"place" => %{"ty" => type}}} ->
        case CallModels.expand(type, context.refs) do
          %{"Adt" => %{"id" => id}} ->
            LLBC.result_type?(id, %{translated: context.translated, references: context.refs}) and
              vector?(type, context)

          _ ->
            false
        end

      _ ->
        false
    end)
  end

  def arguments do
    [
      "--lift-associated-types",
      "*",
      "--treat-box-as-builtin",
      "--ops-to-function-calls",
      "--index-to-function-calls",
      "--reconstruct-fallible-operations",
      "--reconstruct-panic-calls",
      "--reconstruct-asserts",
      "--reconstruct-matches",
      "--hide-marker-traits",
      "--remove-unused-self-clauses",
      "--remove-adt-clauses",
      "--unbind-item-vars",
      "--deallocate-all-locals",
      "--no-gen-tuple-structs"
    ]
  end

  def audit!(preserved, erased, first_party) do
    raw = context(preserved, true)
    normal = context(erased, false)
    ignored = ~w(dest_file preset hide_allocator)

    unless preserved["charon_version"] == erased["charon_version"] and
             preserved["has_errors"] == false and
             raw.translated["crate_name"] == normal.translated["crate_name"] and
             raw.translated["options"]["hide_allocator"] == false and
             normal.translated["options"]["hide_allocator"] == true and
             Map.drop(raw.translated["options"], ignored) ==
               Map.drop(normal.translated["options"], ignored),
           do: raise(ArgumentError, "allocator metadata extraction configuration mismatch")

    for section <- ~w(fun_decls type_decls global_decls) do
      before = declarations(raw, section, first_party)
      after_erasure = declarations(normal, section, first_party)

      unless Enum.sort(Map.keys(before)) == Enum.sort(Map.keys(after_erasure)),
        do: raise(ArgumentError, "allocator metadata has different first-party declarations")

      for {name, original} <- before do
        translated = after_erasure[name]

        unless shape(fields(section, original), raw) == shape(fields(section, translated), normal),
          do: raise(ArgumentError, "allocator metadata type correspondence mismatch: #{name}")
      end
    end

    %{
      global_vectors: true,
      functions: declarations(normal, "fun_decls", first_party) |> Map.keys() |> Enum.sort(),
      source: :allocator_preserving_charon,
      configuration: :same_except_allocator_visibility
    }
  end

  defp fields("fun_decls", function) do
    locals =
      case function["body"] do
        %{"Structured" => body} -> body["locals"]
        _ -> nil
      end

    [function["signature"], locals]
  end

  defp fields("type_decls", type), do: [type["generics"], type["kind"]]
  defp fields("global_decls", global), do: [global["ty"]]

  defp declarations(context, section, first_party) do
    entries =
      for declaration <- context.translated[section],
          declaration &&
            hd(declaration["item_meta"]["name"])["Ident"]
            |> then(fn
              [crate, _] -> crate in first_party
              _ -> false
            end),
          do: {JSON.encode!(declaration["item_meta"]["name"]), declaration}

    unless length(entries) == map_size(Map.new(entries)),
      do: raise(ArgumentError, "ambiguous first-party allocator metadata identity")

    Map.new(entries)
  end

  defp context(document, preserved) do
    translated = document["translated"]

    %{
      translated: translated,
      refs: LLBC.type_references!(document),
      preserved: preserved,
      types: Map.new(for t <- translated["type_decls"], t != nil, do: {t["def_id"], t})
    }
  end

  defp vector?(type, context),
    do:
      any?(CallModels.expand(type, context.refs), fn
        %{"Adt" => %{"id" => id}} -> context.types[id]["item_meta"]["name"] == @vec
        _ -> false
      end)

  defp shape(%{"Value" => [_, type]}, context), do: shape(type, context)
  defp shape(%{"Deduplicated" => id}, context), do: shape(Map.fetch!(context.refs, id), context)

  defp shape(%{"Adt" => %{"id" => id, "generics" => args} = adt}, context) do
    name = context.types[id]["item_meta"]["name"]

    args =
      if context.preserved and name == @vec do
        case args["types"] do
          [element, allocator] ->
            allocator = CallModels.expand(allocator, context.refs)

            unless match?(%{"Adt" => %{"builtin" => nil}}, allocator) and
                     context.types[allocator["Adt"]["id"]]["item_meta"]["name"] == @global and
                     allocator["Adt"]["generics"] == Lynx.Rust.ResourceModels.args([]),
                   do:
                     raise(
                       ArgumentError,
                       "nested vector cleanup requires compiler-confirmed Global allocation"
                     )

            Map.put(args, "types", [element])

          _ ->
            raise ArgumentError, "missing vector allocator metadata"
        end
      else
        args
      end

    %{"Adt" => %{adt | "id" => name, "generics" => shape(args, context)}}
  end

  defp shape(map, context) when is_map(map),
    do: Map.new(Map.drop(map, ["span"]), fn {key, value} -> {key, shape(value, context)} end)

  defp shape(list, context) when is_list(list), do: Enum.map(list, &shape(&1, context))
  defp shape(value, _), do: value

  defp any?(value, predicate) do
    predicate.(value) or
      case value do
        map when is_map(map) -> Enum.any?(Map.values(map), &any?(&1, predicate))
        list when is_list(list) -> Enum.any?(list, &any?(&1, predicate))
        _ -> false
      end
  end
end
