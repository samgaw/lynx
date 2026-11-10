defmodule Lynx.Rust.CleanupFlags do
  @moduledoc false
  alias Lynx.Rust.CallModels

  # rustc guards unwind drops with ordinary boolean locals. Follow only literal
  # assignments to unborrowed scalar booleans. Never infer a flag from ownership,
  # a callee's contract, or the outcome of a potentially panicking operation.
  def lower!(document, first_party) do
    constants = constants(document, %{})
    refs = Lynx.Rust.LLBC.type_references!(document)

    {functions, records} =
      Enum.map_reduce(document["translated"]["fun_decls"], [], fn function, records ->
        with %{"item_meta" => %{"name" => [%{"Ident" => [crate, _]} | _]}} <- function,
             true <- crate in first_party,
             %{"Structured" => body} <- function["body"] do
          borrowed = MapSet.new(borrowed(body))

          flags =
            for local <- body["locals"]["locals"],
                CallModels.expand(local["ty"], refs) == %{"Scalar" => "Bool"},
                not MapSet.member?(borrowed, local["index"]),
                into: MapSet.new(),
                do: local["index"]

          ctx = %{flags: flags, constants: constants, caller: function["def_id"]}
          {block, _, found} = block(body["body"], %{}, ctx, false)
          {put_in(function, ["body", "Structured", "body"], block), found ++ records}
        else
          _ -> {function, records}
        end
      end)

    {put_in(document, ["translated", "fun_decls"], functions), records}
  end

  defp block(%{"statements" => statements} = block, known, ctx, cleanup) do
    {statements, {known, records}} =
      Enum.map_reduce(statements, {known, []}, fn statement, {known, records} ->
        {items, known, found} = statement(statement, known, ctx, cleanup)
        {items, {known, found ++ records}}
      end)

    statements = List.flatten(statements)

    terminal =
      if cleanup,
        do:
          Enum.find_index(
            statements,
            &(&1["kind"] in ["Return", "UnwindResume", "UnwindTerminate"])
          )

    {statements, records} =
      if terminal != nil and terminal + 1 < length(statements) do
        {retained, removed} = Enum.split(statements, terminal + 1)

        record = %{
          kind: :terminal_cleanup_tail,
          caller: ctx.caller,
          statement: List.last(retained)["id"],
          removed: Enum.map(removed, & &1["id"])
        }

        {retained, [record | records]}
      else
        {statements, records}
      end

    {Map.put(block, "statements", statements), known, records}
  end

  defp statement(%{"kind" => %{"Switch" => switch}} = statement, known, ctx, cleanup) do
    value =
      case switch["data"]["scrutinee"] do
        %{"Value" => operand} -> boolean(operand, known, ctx)
        _ -> :unknown
      end

    if cleanup and is_boolean(value) do
      data = switch["data"]

      index =
        Enum.find_value(data["branches"], data["fallback"], fn [constant, index] ->
          if constant(constant, ctx.constants) == value, do: index
        end)

      # An unknown branch label could also match: do not simplify that switch.
      if Enum.all?(data["branches"], fn [label, _] ->
           is_boolean(constant(label, ctx.constants))
         end) do
        {selected, known, records} =
          block(Enum.fetch!(switch["branches"], index), known, ctx, true)

        record = %{
          kind: :constant_cleanup_branch,
          caller: ctx.caller,
          statement: statement["id"],
          value: value,
          selected_branch: index
        }

        {selected["statements"], known, [record | records]}
      else
        branches(statement, switch, known, ctx, cleanup)
      end
    else
      branches(statement, switch, known, ctx, cleanup)
    end
  end

  defp statement(%{"kind" => %{"Call" => call}} = statement, known, ctx, _cleanup) do
    # A call cannot mutate an unborrowed local. Its destination is unavailable
    # on unwind and receives an unknown value on normal return.
    {unwind, _, records} = block(call["on_unwind"], known, ctx, true)
    known = Map.delete(known, root(call["dest"]))
    {[put_in(statement, ["kind", "Call", "on_unwind"], unwind)], known, records}
  end

  defp statement(%{"kind" => %{"Panic" => panic}} = statement, known, ctx, _) do
    {unwind, _, records} = block(panic["on_unwind"], known, ctx, true)
    {[put_in(statement, ["kind", "Panic", "on_unwind"], unwind)], %{}, records}
  end

  defp statement(%{"kind" => %{"Assign" => [place, value]}} = statement, known, ctx, _) do
    local = root(place)

    evaluated =
      case value do
        %{"Use" => [operand, _]} -> boolean(operand, known, ctx)
        _ -> :unknown
      end

    known =
      if MapSet.member?(ctx.flags, local) and is_boolean(evaluated),
        do: Map.put(known, local, evaluated),
        else: Map.delete(known, local)

    {[statement], known, []}
  end

  defp statement(%{"kind" => %{"StorageDead" => local}} = statement, known, _, _),
    do: {[statement], Map.delete(known, local), []}

  # Do not carry facts through loops or unfamiliar control flow. Their contents
  # remain intact and must pass the ordinary implementation/cleanup audits.
  defp statement(%{"kind" => kind} = statement, known, _, _)
       when is_map_key(kind, "StorageLive"),
       do: {[statement], Map.delete(known, kind["StorageLive"]), []}

  defp statement(statement, _known, _, _), do: {[statement], %{}, []}

  defp branches(statement, switch, known, ctx, cleanup) do
    {branches, records} =
      Enum.map_reduce(switch["branches"], [], fn branch, records ->
        {branch, _, found} = block(branch, known, ctx, cleanup)
        {branch, found ++ records}
      end)

    {[put_in(statement, ["kind", "Switch", "branches"], branches)], %{}, records}
  end

  defp boolean(%{"Const" => value}, _, ctx), do: constant(value, ctx.constants)

  defp boolean(%{"Copy" => %{"kind" => %{"Local" => id}}}, known, _),
    do: Map.get(known, id, :unknown)

  defp boolean(%{"Move" => %{"kind" => %{"Local" => id}}}, known, _),
    do: Map.get(known, id, :unknown)

  defp boolean(_, _, _), do: :unknown

  defp constant(%{"Value" => [_, [%{"Bool" => value}, _]]}, _), do: value
  defp constant(%{"Deduplicated" => id}, constants), do: Map.get(constants, id, :unknown)
  defp constant(_, _), do: :unknown

  defp constants(%{"Value" => [id, [%{"Bool" => value}, _]]}, found) do
    if Map.has_key?(found, id) and found[id] != value,
      do: raise(ArgumentError, "inconsistent cleanup boolean constant identity")

    Map.put(found, id, value)
  end

  defp constants(map, found) when is_map(map),
    do: Enum.reduce(Map.values(map), found, &constants/2)

  defp constants(list, found) when is_list(list), do: Enum.reduce(list, found, &constants/2)
  defp constants(_, found), do: found

  defp root(%{"kind" => %{"Local" => id}}), do: id
  defp root(%{"kind" => %{"Projection" => [base, _]}}), do: root(base)
  defp root(_), do: nil

  defp borrowed(%{"Ref" => %{"place" => place}}), do: [root(place)]
  defp borrowed(%{"RawPtr" => %{"place" => place}}), do: [root(place)]
  defp borrowed(map) when is_map(map), do: Enum.flat_map(Map.values(map), &borrowed/1)
  defp borrowed(list) when is_list(list), do: Enum.flat_map(list, &borrowed/1)
  defp borrowed(_), do: []
end
