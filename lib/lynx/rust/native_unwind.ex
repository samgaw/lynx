defmodule Lynx.Rust.NativeUnwind do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, NativeDrops}

  # Reuse the Aeneas preset's operations without the two assertion-resugaring
  # passes, which can erase cleanup. This is deliberately an explicit opt-in.
  def charon_arguments(:reject), do: ["--preset=aeneas"]

  def charon_arguments(:assertions) do
    [
      "--lift-associated-types",
      "*",
      "--treat-box-as-builtin",
      "--ops-to-function-calls",
      "--index-to-function-calls",
      "--reconstruct-panic-calls",
      "--reconstruct-matches",
      "--hide-marker-traits",
      "--hide-allocator",
      "--remove-unused-self-clauses",
      "--remove-adt-clauses",
      "--unbind-item-vars",
      "--deallocate-all-locals",
      "--no-gen-tuple-structs"
    ]
  end

  def charon_arguments(other),
    do: raise(ArgumentError, "unsupported Rust unwind model: #{inspect(other)}")

  def backend_arguments!(:reject, _tools), do: []

  def backend_arguments!(:assertions, tools) do
    unless File.read!(Path.join(tools, "lynx-toolchain")) =~ "assertion-unwind-v1",
      do: raise(ArgumentError, "assertion unwind requires the pinned assertion-unwind backend")

    ["-assertion-unwind-input"]
  end

  def lower!(document, first_party) do
    translated = document["translated"]
    refs = LLBC.type_references!(document)

    {functions, records} =
      Enum.map_reduce(translated["fun_decls"], [], fn function, records ->
        if function && match?(%{"Structured" => _}, function["body"]) &&
             first_party?(hd(function["item_meta"]["name"])["Ident"], first_party) do
          context = %{function: function, translated: translated, refs: refs}
          {body, records} = walk(function["body"], context, records)
          {Map.put(function, "body", body), records}
        else
          {function, records}
        end
      end)

    {put_in(document, ["translated", "fun_decls"], functions), Enum.reverse(records)}
  end

  # The closed mutex/normal-guard destruction models update the cell or
  # exhaust verification; they cannot raise a Rust panic. Compiler cleanup behind
  # that call is unreachable in this model. Validate every concrete dictionary
  # before omitting its unwind-only block, including calls introduced by lowering.
  def nonpanicking_drops!(document) do
    translated = document["translated"]
    refs = LLBC.type_references!(document)
    functions = Enum.reject(translated["fun_decls"], &is_nil/1)

    models =
      for function <- functions,
          model = NativeDrops.resolve(function, translated, refs),
          model != nil,
          into: %{},
          do: {function["def_id"], model}

    case NativeDrops.audit(functions, models, translated, refs) do
      :ok -> :ok
      {:error, function, message} -> LLBC.failure!(function, translated, message)
    end

    prune_calls(document, MapSet.new(Map.keys(models)), [])
  end

  defp prune_calls(
         %{
           "Call" =>
             %{
               "call" => %{"func" => %{"Regular" => %{"kind" => %{"Fun" => id}}}},
               "on_unwind" => cleanup
             } = call
         } = node,
         ids,
         records
       ) do
    if MapSet.member?(ids, id) and cleanup["statements"] != [] do
      record = %{kind: :nonpanicking_drop_call, function: id, cleanup_block: cleanup["id"]}

      {Map.put(node, "Call", Map.put(call, "on_unwind", Map.put(cleanup, "statements", []))),
       [record | records]}
    else
      prune_children(node, ids, records)
    end
  end

  defp prune_calls(value, ids, records), do: prune_children(value, ids, records)

  defp prune_children(map, ids, records) when is_map(map) do
    {pairs, records} =
      Enum.map_reduce(Enum.sort(map), records, fn {key, value}, records ->
        {value, records} = prune_calls(value, ids, records)
        {{key, value}, records}
      end)

    {Map.new(pairs), records}
  end

  defp prune_children(list, ids, records) when is_list(list),
    do: Enum.map_reduce(list, records, &prune_calls(&1, ids, &2))

  defp prune_children(value, _, records), do: {value, records}

  defp first_party?([name, _], crates), do: name in crates
  defp first_party?(_, _), do: false

  defp walk(%{"statements" => statements} = block, ctx, records) do
    {groups, records} =
      Enum.map_reduce(statements, records, fn statement, records ->
        case statement["kind"] do
          %{"Panic" => %{"name" => _, "on_unwind" => cleanup} = panic} ->
            statements = cleanup!(cleanup, ctx)

            terminal =
              put_in(
                statement,
                ["kind", "Panic"],
                Map.put(panic, "on_unwind", Map.put(cleanup, "statements", []))
              )

            record = %{
              kind: :panic_cleanup,
              caller: ctx.function["def_id"],
              panic: statement["id"],
              cleanup: Enum.map(statements, & &1["id"])
            }

            {statements ++ [terminal], [record | records]}

          _ ->
            {statement, records} = walk_children(statement, ctx, records)
            {[statement], records}
        end
      end)

    {Map.put(block, "statements", List.flatten(groups)), records}
  end

  defp walk(value, ctx, records), do: walk_children(value, ctx, records)

  defp walk_children(map, ctx, records) when is_map(map) do
    {pairs, records} =
      Enum.map_reduce(Enum.sort(map), records, fn {key, value}, records ->
        {value, records} = walk(value, ctx, records)
        {{key, value}, records}
      end)

    {Map.new(pairs), records}
  end

  defp walk_children(list, ctx, records) when is_list(list),
    do: Enum.map_reduce(list, records, &walk(&1, ctx, &2))

  defp walk_children(value, _, records), do: {value, records}

  defp cleanup!(%{"statements" => statements}, ctx) when is_list(statements) do
    case Enum.split(statements, -1) do
      {prefix, [%{"kind" => "UnwindResume"}]} ->
        prefix!(prefix, ctx)
        prefix

      _ ->
        reject!(ctx)
    end
  end

  defp cleanup!(_, ctx), do: reject!(ctx)

  defp prefix!(statements, ctx) do
    for statement <- statements do
      case statement["kind"] do
        %{"StorageDead" => local} when is_integer(local) ->
          :ok

        %{"Drop" => drop} ->
          unless match?(
                   {:ok, %{native_kind: :mutex}},
                   NativeDrops.site(drop, ctx.translated, ctx.refs)
                 ),
                 do: reject!(ctx)

        %{
          "Switch" => %{"data" => %{"scrutinee" => %{"Value" => operand}}, "branches" => branches}
        } ->
          place =
            case operand do
              %{"Copy" => place} -> place
              %{"Move" => place} -> place
              _ -> reject!(ctx)
            end

          case place do
            %{"kind" => %{"Local" => _}, "ty" => type} ->
              unless CallModels.expand(type, ctx.refs) == %{"Scalar" => "Bool"}, do: reject!(ctx)

            _ ->
              reject!(ctx)
          end

          for branch <- branches, do: prefix!(branch["statements"], ctx)

        _ ->
          reject!(ctx)
      end
    end
  end

  defp reject!(ctx),
    do:
      LLBC.failure!(
        ctx.function,
        ctx.translated,
        "unsupported assertion unwind cleanup: expected local destructor-free Mutex destruction, storage cleanup and a final UnwindResume"
      )
end
