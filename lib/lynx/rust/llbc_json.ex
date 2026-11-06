defmodule Lynx.Rust.LLBCJson do
  @moduledoc false

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
