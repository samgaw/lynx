defmodule Lynx.Rust.ReferenceCopies do
  @moduledoc false
  alias Lynx.Rust.{CallModels, DropModels, LLBC, LLBCJson}

  # Charon represents rustc CopyForDeref as an unretagged Copy of &mut T.
  # Aeneas cannot copy a mutable borrow. Eliminate only a compiler temporary
  # used exactly once, through dereference in the immediately next assignment.
  # No operation can change the source pointer between its load and use.
  def lower!(document) do
    refs = LLBC.type_references!(document)

    {functions, records} =
      Enum.map_reduce(document["translated"]["fun_decls"], [], fn
        %{"body" => %{"Structured" => _}} = function, records ->
          {body, found} = blocks(function["body"], function, refs)
          {Map.put(function, "body", body), records ++ found}

        function, records ->
          {function, records}
      end)

    lowered = put_in(document, ["translated", "fun_decls"], functions)

    if records == [] do
      {document, []}
    else
      {lowered
       |> LLBCJson.restore_type_references!(document)
       |> LLBCJson.restore_spans!(document), records}
    end
  end

  defp blocks(%{"statements" => statements} = block, function, refs) do
    {statements, records, removed} = statements(statements, function, refs, [], MapSet.new())

    statements =
      Enum.reject(statements, fn statement ->
        case statement["kind"] do
          %{"StorageLive" => id} -> MapSet.member?(removed, id)
          %{"StorageDead" => id} -> MapSet.member?(removed, id)
          _ -> false
        end
      end)

    {statements, nested} =
      Enum.map_reduce(statements, [], fn statement, records ->
        {statement, more} = blocks(statement, function, refs)
        {statement, records ++ more}
      end)

    {Map.put(block, "statements", statements), records ++ nested}
  end

  defp blocks(map, function, refs) when is_map(map) do
    {pairs, records} =
      Enum.map_reduce(map, [], fn {key, value}, records ->
        {value, more} = blocks(value, function, refs)
        {{key, value}, records ++ more}
      end)

    {Map.new(pairs), records}
  end

  defp blocks(list, function, refs) when is_list(list) do
    Enum.map_reduce(list, [], fn value, records ->
      {value, more} = blocks(value, function, refs)
      {value, records ++ more}
    end)
  end

  defp blocks(value, _, _), do: {value, []}

  defp statements([copy, next | rest], function, refs, records, removed) do
    with %{
           "Assign" => [
             %{"kind" => %{"Local" => local}, "ty" => target},
             %{"Use" => [%{"Copy" => source}, "No"]}
           ]
         } <- copy["kind"],
         %{"Ref" => [_, inner, "Mut"]} <- CallModels.expand(target, refs),
         %{"Ref" => [_, ^inner, "Mut"]} <- CallModels.expand(source["ty"], refs),
         true <- local > function["body"]["Structured"]["locals"]["arg_count"],
         true <- DropModels.primitive_scalar?(inner),
         true <- local_uses(function["body"], local) == 2,
         true <- local_uses(source, local) == 0,
         %{"Assign" => [_, value]} <- next["kind"],
         true <- simple?(value, refs),
         {changed, 1} <- replace(next, local, source, refs, inner) do
      record = %{
        function_id: function["def_id"],
        statement_id: copy["id"],
        use_statement_id: next["id"],
        local: local,
        source: source,
        label: "Adjacent single-dereference unretagged mutable-reference copy normalization"
      }

      statements([changed | rest], function, refs, [record | records], MapSet.put(removed, local))
    else
      _ ->
        {tail, records, removed} = statements([next | rest], function, refs, records, removed)
        {[copy | tail], records, removed}
    end
  end

  defp statements(rest, _, _, records, removed), do: {rest, records, removed}

  defp simple?(%{"UnaryOp" => [_, operand]}, refs), do: scalar_operand?(operand, refs)

  defp simple?(%{"BinaryOp" => [_, left, right]}, refs),
    do: scalar_operand?(left, refs) and scalar_operand?(right, refs)

  defp simple?(%{"Use" => [operand, _]}, refs), do: scalar_operand?(operand, refs)
  defp simple?(_, _), do: false

  defp scalar_operand?(%{"Move" => place}, refs),
    do: DropModels.primitive_scalar?(CallModels.expand(place["ty"], refs))

  defp scalar_operand?(%{"Copy" => place}, refs),
    do: DropModels.primitive_scalar?(CallModels.expand(place["ty"], refs))

  defp scalar_operand?(_, _), do: false

  defp replace(
         %{"kind" => %{"Projection" => [%{"kind" => %{"Local" => local}}, "Deref"]}, "ty" => ty} =
           place,
         local,
         source,
         refs,
         inner
       ) do
    if CallModels.expand(ty, refs) == inner,
      do: {put_in(place, ["kind", "Projection"], [source, "Deref"]), 1},
      else: {place, 0}
  end

  defp replace(map, local, source, refs, inner) when is_map(map) do
    {pairs, n} =
      Enum.map_reduce(map, 0, fn {key, value}, n ->
        {value, more} = replace(value, local, source, refs, inner)
        {{key, value}, n + more}
      end)

    {Map.new(pairs), n}
  end

  defp replace(list, local, source, refs, inner) when is_list(list) do
    Enum.map_reduce(list, 0, fn value, n ->
      {value, more} = replace(value, local, source, refs, inner)
      {value, n + more}
    end)
  end

  defp replace(value, _, _, _, _), do: {value, 0}

  defp local_uses(%{"Local" => local}, local), do: 1

  defp local_uses(map, local) when is_map(map),
    do: Enum.sum(Enum.map(Map.values(map), &local_uses(&1, local)))

  defp local_uses(list, local) when is_list(list),
    do: Enum.sum(Enum.map(list, &local_uses(&1, local)))

  defp local_uses(_, _), do: 0
end
