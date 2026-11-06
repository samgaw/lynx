defmodule Lynx.Rust.LLBCJson do
  @moduledoc false

  # Charon's compiler query is audit metadata. The pinned Aeneas reader uses
  # an older, exact record schema; remove only this field at its input boundary.
  # Keep the original query in the audited document and raw extraction hash.
  def drop_query_metadata!(document) do
    {types, queries} =
      Enum.map_reduce(document["translated"]["type_decls"], [], fn
        nil, queries ->
          {nil, queries}

        type, queries ->
          case Map.pop(type, "needs_drop", :missing) do
            {value, type} when is_boolean(value) or is_nil(value) ->
              {type, [%{type_id: type["def_id"], needs_drop: value} | queries]}

            {:missing, type} ->
              {type, queries}

            _ ->
              raise ArgumentError, "invalid compiler drop query metadata"
          end
      end)

    {put_in(document, ["translated", "type_decls"], types), Enum.reverse(queries)}
  end

  # Removing an unreachable block can remove a span's first serialized value,
  # while a later statement still refers to its ID. Span IDs have their own
  # family: never resolve them through type/constant/trait reference tables.
  def restore_spans!(document, original) do
    spans = span_values(original, %{})
    restore_spans(document, spans)
  end

  # A concrete trait dictionary can first occur in unreachable unwind cleanup.
  # Rehydrate only its own hash-cons family before subsequent audits/lowering;
  # trait IDs and type IDs deliberately use separate tables.
  def restore_trait_references!(document, original) do
    traits = trait_values(original, %{})
    restore_traits(document, traits, [])
  end

  defp trait_values(%{"Value" => [id, %{"kind" => _, "trait_decl_ref" => _} = value]}, refs) do
    if Map.has_key?(refs, id) and refs[id] != value,
      do: raise(ArgumentError, "inconsistent LLBC trait-reference identity")

    trait_values(value, Map.put(refs, id, value))
  end

  defp trait_values(map, refs) when is_map(map), do: trait_values(Map.values(map), refs)
  defp trait_values(list, refs) when is_list(list), do: Enum.reduce(list, refs, &trait_values/2)
  defp trait_values(_, refs), do: refs

  defp restore_traits(map, refs, seen) when is_map(map) do
    Map.new(map, fn
      {"trait_refs", values} -> {"trait_refs", Enum.map(values, &restore_trait(&1, refs, seen))}
      {key, value} -> {key, restore_traits(value, refs, seen)}
    end)
  end

  defp restore_traits(list, refs, seen) when is_list(list),
    do: Enum.map(list, &restore_traits(&1, refs, seen))

  defp restore_traits(value, _, _), do: value

  defp restore_trait(
         %{"regions" => _, "outlives" => _, "skip_binder" => wrapped} = ref,
         refs,
         seen
       ) do
    case wrapped do
      %{"Deduplicated" => id} ->
        if id in seen, do: raise(ArgumentError, "cyclic LLBC trait reference")
        value = Map.get(refs, id) || raise(ArgumentError, "missing LLBC trait reference #{id}")
        put_in(ref, ["skip_binder"], %{"Value" => [id, restore_traits(value, refs, [id | seen])]})

      %{"Value" => [id, value]} ->
        put_in(ref, ["skip_binder"], %{"Value" => [id, restore_traits(value, refs, [id | seen])]})

      _ ->
        restore_traits(ref, refs, seen)
    end
  end

  defp restore_trait(ref, refs, seen), do: restore_traits(ref, refs, seen)

  defp span_values(%{"span" => %{"Value" => [id, value]}} = map, spans) do
    case Map.fetch(spans, id) do
      {:ok, other} when other != value -> raise ArgumentError, "inconsistent LLBC span identity"
      _ -> span_values(Map.values(map), Map.put(spans, id, value))
    end
  end

  defp span_values(map, spans) when is_map(map), do: span_values(Map.values(map), spans)
  defp span_values(list, spans) when is_list(list), do: Enum.reduce(list, spans, &span_values/2)
  defp span_values(_, spans), do: spans

  defp restore_spans(map, spans) when is_map(map) do
    Map.new(map, fn
      {"span", %{"Deduplicated" => id}} ->
        {"span",
         %{
           "Untagged" =>
             Map.get(spans, id) || raise(ArgumentError, "missing LLBC span identity #{id}")
         }}

      {key, value} ->
        {key, restore_spans(value, spans)}
    end)
  end

  defp restore_spans(list, spans) when is_list(list),
    do: Enum.map(list, &restore_spans(&1, spans))

  defp restore_spans(value, _), do: value

  # The pinned charon-ml reader matches record fields in serde declaration order.
  # Preserve the original order when editing LLBC, including unchanged nested
  # records. New records use an observed schema, never alphabetic map ordering.
  def encode_like!(document, original) do
    {ordered, _, _} =
      JSON.decode(File.read!(original), :ok,
        object_finish: fn fields, acc -> {{:object, Enum.reverse(fields)}, acc} end
      )

    orders = collect(ordered, %{})
    encoded = document |> encode(ordered, orders) |> IO.iodata_to_binary()

    unless JSON.decode!(encoded) === document,
      do: raise(ArgumentError, "native LLBC serialization changed the lowered document")

    encoded
  end

  defp collect({:object, fields}, orders) do
    keys = Enum.map(fields, &elem(&1, 0))
    key = Enum.sort(keys)

    orders =
      case Map.fetch(orders, key) do
        :error -> Map.put(orders, key, keys)
        {:ok, ^keys} -> orders
        {:ok, _} -> Map.put(orders, key, :ambiguous)
      end

    Enum.reduce(fields, orders, fn {_, value}, orders -> collect(value, orders) end)
  end

  defp collect(list, orders) when is_list(list), do: Enum.reduce(list, orders, &collect/2)
  defp collect(_, orders), do: orders

  defp encode(map, original, orders) when is_map(map) do
    {old_fields, old_keys} =
      case original do
        {:object, fields} -> {Map.new(fields), Enum.map(fields, &elem(&1, 0))}
        _ -> {%{}, []}
      end

    keys = Enum.sort(Map.keys(map))

    order =
      cond do
        Enum.sort(old_keys) == keys ->
          old_keys

        # Remove only the compiler query from the exact TypeDecl record schema.
        keys == ~w(def_id generics item_meta kind layout marker_traits ptr_metadata src) and
            Enum.sort(old_keys) == Enum.sort(["needs_drop" | keys]) ->
          List.delete(old_keys, "needs_drop")

        # TraitRef is introduced when lowering a Drop to a consuming call. Its
        # precise shape is fixed by the pinned LLBC schema and checked by audit.
        keys == ["kind", "trait_decl_ref"] ->
          ["kind", "trait_decl_ref"]

        keys == ["args", "func", "safety"] ->
          ["func", "args", "safety"]

        keys == ["call", "dest", "on_unwind"] ->
          ["call", "dest", "on_unwind"]

        length(keys) <= 1 ->
          keys

        true ->
          case Map.get(orders, keys) do
            value when is_list(value) ->
              value

            _ ->
              raise ArgumentError,
                    "missing or ambiguous LLBC record field order: #{inspect(keys)}"
          end
      end

    fields =
      Enum.map(order, fn key ->
        [JSON.encode!(key), ":", encode(Map.fetch!(map, key), old_fields[key], orders)]
      end)

    ["{", Enum.intersperse(fields, ","), "}"]
  end

  defp encode(list, original, orders) when is_list(list) do
    previous = if is_list(original), do: List.to_tuple(original), else: {}

    values =
      Enum.with_index(list)
      |> Enum.map(fn {value, index} ->
        old = if index < tuple_size(previous), do: elem(previous, index), else: nil
        encode(value, old, orders)
      end)

    ["[", Enum.intersperse(values, ","), "]"]
  end

  defp encode(value, _, _), do: JSON.encode!(value)
end
