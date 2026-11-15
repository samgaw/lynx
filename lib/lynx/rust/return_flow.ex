defmodule Lynx.Rust.ReturnFlow do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBCJson}

  # Intraprocedural non-fallthrough only. A call may fail or diverge, but cannot
  # jump past a following Return. Loops and outer break/continue are unknown.
  def returns?(statements, translated, refs), do: flow(statements, translated, refs) == :return

  defp flow([], _, _), do: :fallthrough
  defp flow([%{"kind" => "Return"} | _], _, _), do: :return

  defp flow([%{"kind" => %{"Switch" => switch}} | rest], translated, refs) do
    if exhaustive?(switch, translated, refs) do
      flows = Enum.map(switch["branches"], &flow(&1["statements"], translated, refs))

      cond do
        :unknown in flows -> :unknown
        Enum.all?(flows, &(&1 == :return)) -> :return
        true -> flow(rest, translated, refs)
      end
    else
      :unknown
    end
  end

  defp flow([%{"kind" => "Nop"} | rest], translated, refs), do: flow(rest, translated, refs)

  defp flow([%{"kind" => kind} | rest], translated, refs) when is_map(kind) do
    if Enum.any?(~w(Assign Call StorageLive StorageDead), &Map.has_key?(kind, &1)),
      do: flow(rest, translated, refs),
      else: :unknown
  end

  defp flow(_, _, _), do: :unknown

  defp exhaustive?(%{"data" => data, "branches" => branches}, translated, refs)
       when is_list(branches) and branches != [] do
    data =
      data
      |> LLBCJson.restore_constant_references!(%{"translated" => translated})
      |> CallModels.expand(refs)

    valid = fn index -> is_integer(index) and index >= 0 and index < length(branches) end
    mappings = data["branches"]

    mapped =
      is_list(mappings) and
        Enum.all?(mappings, fn
          [_, index] -> valid.(index)
          _ -> false
        end)

    mapped and
      if is_nil(data["fallback"]),
        do: complete_cases?(data, translated, refs),
        else: valid.(data["fallback"])
  end

  defp exhaustive?(_, _, _), do: false

  defp complete_cases?(
         %{
           "scrutinee" => %{"Discriminant" => %{"ty" => %{"Adt" => adt}}},
           "branches" => mappings
         },
         translated,
         refs
       ) do
    type = Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == adt["id"]))

    case type && CallModels.expand(type["kind"], refs) do
      %{"Enum" => variants} when is_list(variants) and variants != [] ->
        tags =
          Enum.map(mappings, fn
            [[%{"Discriminant" => [^adt, variant]}, _], _] -> variant
            _ -> nil
          end)

        ids = Enum.map(variants, & &1["id"])

        Enum.all?(ids, &(is_integer(&1) and &1 >= 0)) and
          length(Enum.uniq(ids)) == length(ids) and Enum.sort(tags) == Enum.sort(ids)

      _ ->
        false
    end
  end

  defp complete_cases?(%{"scrutinee" => %{"Value" => operand}, "branches" => mappings}, _, _) do
    type =
      case operand do
        %{"Copy" => %{"ty" => type}} -> type
        %{"Move" => %{"ty" => type}} -> type
        _ -> nil
      end

    tags =
      Enum.map(mappings, fn
        [[%{"Bool" => value}, %{"Scalar" => "Bool"}], _] -> value
        _ -> nil
      end)

    type == %{"Scalar" => "Bool"} and Enum.sort(tags) == [false, true]
  end

  defp complete_cases?(_, _, _), do: false
end
