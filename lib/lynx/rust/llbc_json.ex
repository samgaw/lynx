defmodule Lynx.Rust.LLBCJson do
  @moduledoc false

  # Compiler queries and extraction flags are retained in the audit and raw
  # extraction hash. Remove their known fields only at the input boundary of
  # Aeneas's older, exact record schema.
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

    document = put_in(document, ["translated", "type_decls"], types)

    document =
      Enum.reduce(
        ~w(immediate_futures suspending_futures cancelling_futures owned_drops),
        document,
        fn field, document ->
          case get_in(document, ["translated", "options", field]) do
            nil ->
              document

            value when is_boolean(value) ->
              update_in(document, ["translated", "options"], &Map.delete(&1, field))

            _ ->
              raise ArgumentError, "invalid compiler extraction metadata"
          end
        end
      )

    {document, Enum.reverse(queries)}
  end

  # Removing an unreachable block can remove a span's first serialized value,
  # while a later statement still refers to its ID. Span IDs have their own
  # family: never resolve them through type/constant/trait reference tables.
  def restore_spans!(document, original) do
    spans = span_values(original, %{})
    restore_spans(document, spans)
  end

  # Cleanup pruning can remove the first serialized type or constant value.
  # Rehydrate explicit positions using separate tables for each ID family.
  def restore_type_references!(document, original) do
    document = restore_constant_references!(document, original)
    original = restore_constant_references!(original, original)

    refs =
      merge_references!(
        Lynx.Rust.LLBC.type_references!(original),
        Lynx.Rust.LLBC.type_references!(document),
        "type"
      )

    restore_types(document, refs)
  end

  # Rehydrate constants before another cleanup analysis, without expanding type
  # references twice or mixing independently hash-consed reference families.
  def restore_constant_references!(document, original) do
    # Cleanup lowering rehydrates trait dictionaries, including those inside
    # constant calls. Compare equal representations before checking identity.
    original = restore_trait_references!(original, original)
    document = restore_trait_references!(document, original)

    constants =
      merge_references!(
        constant_values(original, %{}),
        constant_values(document, %{}),
        "constant"
      )

    restore_constants(document, constants)
  end

  # Global values use the constant-value table too. A repeated literal can be
  # serialized once and referenced by a different global declaration; never
  # resolve that reference through the independently numbered type table.
  def restore_global_constant_values!([], _document), do: []

  def restore_global_constant_values!(globals, document) do
    document = restore_trait_references!(document, document)
    constants = constant_values(document, %{})

    Enum.map(
      globals,
      &Map.update!(&1, "value", fn value -> restore_constant(value, constants) end)
    )
  end

  defp merge_references!(left, right, kind) do
    Map.merge(left, right, fn id, previous, value ->
      if previous != value, do: raise(ArgumentError, "inconsistent LLBC #{kind} reference #{id}")
      value
    end)
  end

  defp constant_values(%{"Value" => [id, [kind, _type] = value]} = node, refs)
       when is_map(kind) do
    refs = merge_references!(refs, %{id => value}, "constant")
    constant_values(Map.values(node), refs)
  end

  defp constant_values(map, refs) when is_map(map), do: constant_values(Map.values(map), refs)

  defp constant_values(list, refs) when is_list(list),
    do: Enum.reduce(list, refs, &constant_values/2)

  defp constant_values(_, refs), do: refs

  defp restore_constants(%{"scrutinee" => _, "branches" => branches} = data, refs) do
    Map.new(data, fn
      {"branches", _} ->
        {"branches",
         Enum.map(branches, fn [value, branch] -> [restore_constant(value, refs), branch] end)}

      {key, value} ->
        {key, restore_constants(value, refs)}
    end)
  end

  defp restore_constants(map, refs) when is_map(map) do
    Map.new(map, fn
      {"Const", value} ->
        {"Const", restore_constant(value, refs)}

      {"Array", [element, length, sized]} ->
        {"Array",
         [
           restore_constants(element, refs),
           restore_constant(length, refs),
           restore_constants(sized, refs)
         ]}

      {"const_generics", values} ->
        {"const_generics", Enum.map(values, &restore_constant(&1, refs))}

      {key, value} ->
        {key, restore_constants(value, refs)}
    end)
  end

  defp restore_constants(list, refs) when is_list(list),
    do: Enum.map(list, &restore_constants(&1, refs))

  defp restore_constants(value, _), do: value

  defp restore_constant(%{"Deduplicated" => id}, refs) do
    value = Map.get(refs, id) || raise(ArgumentError, "missing LLBC constant reference #{id}")
    %{"Value" => [id, restore_constants(value, refs)]}
  end

  defp restore_constant(value, refs), do: restore_constants(value, refs)

  defp restore_types(%{"Value" => [id, [kind, type]]}, refs) when is_map(kind) do
    %{"Value" => [id, [restore_types(kind, refs), restore_type(type, refs, [])]]}
  end

  defp restore_types(map, refs) when is_map(map) do
    Map.new(map, fn
      {key, type} when key in ["ty", "output"] ->
        {key, restore_type(type, refs, [])}

      {key, types} when key in ["types", "inputs"] and is_list(types) ->
        {key, Enum.map(types, &restore_type(&1, refs, []))}

      {key, value} ->
        {key, restore_types(value, refs)}
    end)
  end

  defp restore_types(list, refs) when is_list(list), do: Enum.map(list, &restore_types(&1, refs))
  defp restore_types(value, _), do: value

  defp restore_type(%{"Deduplicated" => id}, refs, seen) do
    if id in seen, do: raise(ArgumentError, "cyclic LLBC type reference")
    value = Map.get(refs, id) || raise(ArgumentError, "missing LLBC type reference #{id}")
    restore_type(%{"Value" => [id, value]}, refs, seen)
  end

  defp restore_type(%{"Value" => [id, value]}, refs, seen) do
    value =
      case value do
        %{"Ref" => [region, type, kind]} ->
          %{"Ref" => [region, restore_type(type, refs, [id | seen]), kind]}

        %{"RawPtr" => [type, kind]} ->
          %{"RawPtr" => [restore_type(type, refs, [id | seen]), kind]}

        %{"Slice" => [type, sized]} ->
          %{"Slice" => [restore_type(type, refs, [id | seen]), restore_types(sized, refs)]}

        %{"Array" => [type, size, sized]} ->
          %{
            "Array" => [
              restore_type(type, refs, [id | seen]),
              restore_types(size, refs),
              restore_types(sized, refs)
            ]
          }

        other ->
          restore_types(other, refs)
      end

    %{"Value" => [id, value]}
  end

  defp restore_type(other, refs, _), do: restore_types(other, refs)

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

        "start_from" in keys and "mir" in keys and "preset" in keys and
          Enum.sort(old_keys -- keys) != [] and
          Enum.all?(
            old_keys -- keys,
            &(&1 in ~w(immediate_futures suspending_futures cancelling_futures owned_drops))
          ) and
            keys -- old_keys == [] ->
          old_keys -- ~w(immediate_futures suspending_futures cancelling_futures owned_drops)

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
