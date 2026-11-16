defmodule Lynx.Rust.CleanupFlags do
  @moduledoc false
  alias Lynx.Rust.CallModels

  # rustc guards unwind drops with ordinary boolean locals. Follow only literal
  # assignments to unborrowed scalar booleans. Never infer a flag from ownership,
  # a callee's contract, or the outcome of a potentially panicking operation.
  def lower!(document, first_party) do
    constants = constants(document, %{})
    discriminants = discriminants(document, %{})
    refs = Lynx.Rust.LLBC.type_references!(document)

    {functions, records} =
      Enum.map_reduce(document["translated"]["fun_decls"], [], fn function, records ->
        with %{"item_meta" => %{"name" => [%{"Ident" => [crate, _]} | _]}} <- function,
             true <-
               crate in first_party or
                 Lynx.Rust.LibraryHelpers.selected?(function, document["translated"]),
             %{"Structured" => body} <- function["body"] do
          borrowed = MapSet.new(borrowed(body))

          flags =
            for local <- body["locals"]["locals"],
                CallModels.expand(local["ty"], refs) == %{"Scalar" => "Bool"},
                not MapSet.member?(borrowed, local["index"]),
                into: MapSet.new(),
                do: local["index"]

          enums = immutable_enum_locals(body, document["translated"], refs)

          ctx = %{
            flags: flags,
            constants: constants,
            caller: function["def_id"],
            enums: enums,
            discriminants: discriminants,
            refs: refs
          }

          {block, _, found} = block(body["body"], %{}, ctx, false)
          {put_in(function, ["body", "Structured", "body"], block), found ++ records}
        else
          _ -> {function, records}
        end
      end)

    {put_in(document, ["translated", "fun_decls"], functions), records}
  end

  # A shared borrow cannot change the tag of the enum value itself. Mutable
  # borrows and raw pointers exclude the complete root, including field borrows.
  def immutable_enum_locals(body, translated, refs) do
    mutable = MapSet.new(mutably_borrowed(body))

    for local <- body["locals"]["locals"],
        not MapSet.member?(mutable, local["index"]),
        %{"Adt" => %{"id" => id, "builtin" => nil} = adt} <- [
          CallModels.expand(local["ty"], refs)
        ],
        declaration = Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id)),
        declaration && is_map(declaration["kind"]),
        variants = declaration["kind"]["Enum"],
        is_list(variants) and variants != [],
        into: %{},
        do: {local["index"], {adt, Enum.map(variants, & &1["id"])}}
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
    enum = enum_switch(switch, ctx)

    value =
      if enum do
        Map.get(known, {:variant, enum.local}, :unknown)
      else
        case switch["data"]["scrutinee"] do
          %{"Value" => operand} -> boolean(operand, known, ctx)
          _ -> :unknown
        end
      end

    if (cleanup and enum) && is_integer(value) do
      index = enum.branches[value]
      {selected, known, records} = block(Enum.fetch!(switch["branches"], index), known, ctx, true)

      record = %{
        kind: :known_variant_cleanup_branch,
        caller: ctx.caller,
        statement: statement["id"],
        local: enum.local,
        variant: value,
        selected_branch: index
      }

      {selected["statements"], known, [record | records]}
    else
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
  end

  defp statement(%{"kind" => %{"Call" => call}} = statement, known, ctx, _cleanup) do
    # A call cannot mutate an unborrowed local. Its destination is unavailable
    # on unwind and receives an unknown value on normal return.
    known = Enum.reduce(moved(call["call"]["args"]), known, &forget(&2, &1))
    {unwind, _, records} = block(call["on_unwind"], known, ctx, true)
    known = forget(known, root(call["dest"]))
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
        else: forget(known, local)

    known = Enum.reduce(moved(value), known, &forget(&2, &1))

    {[statement], known, []}
  end

  defp statement(%{"kind" => %{"StorageDead" => local}} = statement, known, _, _),
    do: {[statement], forget(known, local), []}

  defp statement(
         %{"kind" => %{"Loop" => %{"statements" => _} = body}} = statement,
         _known,
         ctx,
         _cleanup
       ) do
    {body, _, records} = block(body, %{}, ctx, false)
    {[put_in(statement, ["kind", "Loop"], body)], %{}, records}
  end

  # Do not carry facts through loops or unfamiliar control flow. Their contents
  # remain intact and must pass the ordinary implementation/cleanup audits.
  defp statement(%{"kind" => kind} = statement, known, _, _)
       when is_map_key(kind, "StorageLive"),
       do: {[statement], forget(known, kind["StorageLive"]), []}

  defp statement(statement, _known, _, _), do: {[statement], %{}, []}

  defp branches(statement, switch, known, ctx, cleanup) do
    enum = enum_switch(switch, ctx)

    {rows, records} =
      Enum.map_reduce(Enum.with_index(switch["branches"]), [], fn {branch, index}, records ->
        entry =
          if enum do
            case for {variant, target} <- enum.branches, target == index, do: variant do
              [variant] -> Map.put(known, {:variant, enum.local}, variant)
              _ -> Map.delete(known, {:variant, enum.local})
            end
          else
            known
          end

        {branch, facts, found} = block(branch, entry, ctx, cleanup)
        {{branch, facts}, found ++ records}
      end)

    falling = for {branch, facts} <- rows, falls_through?(branch), do: facts

    joined =
      case falling do
        [] ->
          %{}

        [first | rest] ->
          Map.filter(first, fn {key, value} ->
            Enum.all?(rest, &(Map.get(&1, key, :unknown) == value))
          end)
      end

    {[put_in(statement, ["kind", "Switch", "branches"], Enum.map(rows, &elem(&1, 0)))], joined,
     records}
  end

  defp enum_switch(switch, ctx) do
    with %{"Discriminant" => %{"kind" => %{"Local" => local}, "ty" => annotation}} <-
           switch["data"]["scrutinee"],
         {adt, variants} <- ctx.enums[local],
         true <- CallModels.expand(annotation, ctx.refs) == %{"Adt" => adt},
         true <- Enum.uniq(variants) == variants do
      labels =
        Enum.map(switch["data"]["branches"], fn [label, index] ->
          case discriminant(label, ctx.discriminants) do
            {decl, variant} ->
              if CallModels.expand(decl, ctx.refs) == adt and variant in variants and
                   is_integer(index) and index >= 0 and index < length(switch["branches"]),
                 do: {variant, index}

            _ ->
              nil
          end
        end)

      fallback = switch["data"]["fallback"]

      if Enum.all?(labels, & &1) and length(Enum.uniq_by(labels, &elem(&1, 0))) == length(labels) and
           (is_nil(fallback) or
              (is_integer(fallback) and fallback >= 0 and fallback < length(switch["branches"]))) do
        remaining = variants -- Enum.map(labels, &elem(&1, 0))

        if remaining == [] or not is_nil(fallback),
          do: %{local: local, branches: Map.new(labels ++ Enum.map(remaining, &{&1, fallback}))}
      end
    else
      _ -> nil
    end
  end

  defp falls_through?(%{"statements" => statements}) do
    Enum.all?(statements, fn statement ->
      case statement["kind"] do
        terminal when terminal in ["Return", "UnwindResume", "UnwindTerminate"] -> false
        %{"Continue" => _} -> false
        %{"Break" => _} -> false
        %{"Panic" => _} -> false
        %{"Switch" => switch} -> Enum.any?(switch["branches"], &falls_through?/1)
        _ -> true
      end
    end)
  end

  defp forget(known, local), do: known |> Map.delete(local) |> Map.delete({:variant, local})
  defp moved(%{"Move" => place}), do: [root(place)]
  defp moved(map) when is_map(map), do: Enum.flat_map(Map.values(map), &moved/1)
  defp moved(list) when is_list(list), do: Enum.flat_map(list, &moved/1)
  defp moved(_), do: []

  defp discriminant(%{"Value" => [_, [%{"Discriminant" => [adt, variant]}, _]]}, _),
    do: {adt, variant}

  defp discriminant(%{"Deduplicated" => id}, values), do: Map.get(values, id)
  defp discriminant(_, _), do: nil

  defp discriminants(%{"Value" => [id, [%{"Discriminant" => [adt, variant]}, _]]}, values) do
    if Map.has_key?(values, id) and values[id] != {adt, variant},
      do: raise(ArgumentError, "inconsistent cleanup discriminant identity")

    Map.put(values, id, {adt, variant})
  end

  defp discriminants(map, values) when is_map(map),
    do: Enum.reduce(Map.values(map), values, &discriminants/2)

  defp discriminants(list, values) when is_list(list),
    do: Enum.reduce(list, values, &discriminants/2)

  defp discriminants(_, values), do: values

  defp mutably_borrowed(%{"Ref" => %{"place" => place, "kind" => kind}}) when kind != "Shared",
    do: [root(place)]

  defp mutably_borrowed(%{"RawPtr" => %{"place" => place}}), do: [root(place)]

  defp mutably_borrowed(map) when is_map(map),
    do: Enum.flat_map(Map.values(map), &mutably_borrowed/1)

  defp mutably_borrowed(list) when is_list(list), do: Enum.flat_map(list, &mutably_borrowed/1)
  defp mutably_borrowed(_), do: []

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
