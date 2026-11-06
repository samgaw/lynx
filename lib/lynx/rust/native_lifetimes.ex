defmodule Lynx.Rust.NativeLifetimes do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, MutexModels, LockModels}

  # Track consuming ownership on every branch. Potential failure with a live
  # owner requires supported cleanup; borrowed calls need checked nonpanicking
  # bodies. Whole single-field enum payloads may transfer their ownership.
  def audit!(functions, models, translated, refs) do
    Lynx.Rust.NativeBorrows.audit!(functions, models, translated, refs)

    mutexes =
      for type <- translated["type_decls"],
          type &&
            (MutexModels.type?(type) or LockModels.guard?(type, refs) or
               Lynx.Rust.ResourceModels.type?(type)),
          do: type["def_id"]

    types = Map.new(Enum.reject(translated["type_decls"], &is_nil/1), &{&1["def_id"], &1})
    implementations = MapSet.new(functions, & &1["def_id"])
    nonpanicking = Lynx.Rust.NativeBorrows.nonpanicking_calls(functions, models)

    for function <- functions,
        %{"Structured" => body} <- [function["body"]] do
      owners =
        for local <- body["locals"]["locals"],
            contains_native?(CallModels.expand(local["ty"], refs), mutexes, types, refs, []),
            into: MapSet.new(),
            do: local["index"]

      if MapSet.size(owners) > 0 do
        live = MapSet.filter(owners, &(&1 > 0 and &1 <= body["locals"]["arg_count"]))

        context = %{
          owners: owners,
          models: models,
          implementations: implementations,
          nonpanicking: nonpanicking,
          function: function,
          translated: translated,
          types: types,
          refs: refs,
          locals:
            Map.new(body["locals"]["locals"], &{&1["index"], CallModels.expand(&1["ty"], refs)}),
          booleans: boolean_constants(translated, %{})
        }

        unless block!(body["body"], live, context) == :terminal, do: reject!(context)
      end
    end
  end

  # References borrow an owner; they do not own or destroy its native cell.
  defp contains_native?(%{"Ref" => _}, _, _, _, _), do: false

  defp contains_native?(%{"Adt" => %{"id" => id} = adt}, mutexes, types, refs, seen) do
    id in mutexes or
      contains_native?(adt["generics"], mutexes, types, refs, seen) or
      (id not in seen and
         contains_native?(
           CallModels.expand(get_in(types, [id, "kind"]), refs),
           mutexes,
           types,
           refs,
           [id | seen]
         ))
  end

  defp contains_native?(map, mutexes, types, refs, seen) when is_map(map),
    do: Enum.any?(Map.values(map), &contains_native?(&1, mutexes, types, refs, seen))

  defp contains_native?(list, mutexes, types, refs, seen) when is_list(list),
    do: Enum.any?(list, &contains_native?(&1, mutexes, types, refs, seen))

  defp contains_native?(_, _, _, _, _), do: false

  defp block!(block, live, ctx), do: block_state!(block, %{live: live, known: %{}}, ctx)

  defp block_state!(%{"statements" => statements}, state, ctx) do
    Enum.reduce_while(statements, state, fn statement, state ->
      case statement["kind"] do
        %{"Switch" => switch} ->
          case switch!(switch, state, ctx) do
            :terminal -> {:halt, :terminal}
            state -> {:cont, state}
          end

        kind ->
          case statement!(kind, state.live, ctx) do
            :terminal -> {:halt, :terminal}
            live -> {:cont, %{live: live, known: known_after(kind, state.known, ctx)}}
          end
      end
    end)
  end

  defp switch!(%{"data" => data, "branches" => branches}, state, ctx) do
    value =
      case data["scrutinee"] do
        %{"Value" => operand} -> boolean(operand, state.known, ctx)
        _ -> :unknown
      end

    if is_boolean(value) do
      index =
        Enum.find_value(data["branches"], data["fallback"], fn [constant, index] ->
          if constant_boolean(constant, ctx) == value, do: index
        end)

      block_state!(Enum.fetch!(branches, index), state, ctx)
    else
      states =
        Enum.map(branches, &block_state!(&1, state, ctx)) |> Enum.reject(&(&1 == :terminal))

      case states do
        [] ->
          :terminal

        [first | rest] ->
          unless Enum.all?(rest, &MapSet.equal?(&1.live, first.live)), do: reject!(ctx)

          known =
            Map.filter(first.known, fn {id, value} ->
              Enum.all?(rest, &(&1.known[id] == value))
            end)

          %{first | known: known}
      end
    end
  end

  defp known_after(%{"Assign" => [%{"kind" => %{"Local" => local}}, value]}, known, ctx) do
    value =
      case value do
        %{"Use" => [operand, _]} -> boolean(operand, known, ctx)
        _ -> :unknown
      end

    if is_boolean(value), do: Map.put(known, local, value), else: Map.delete(known, local)
  end

  defp known_after(%{"StorageDead" => local}, known, _), do: Map.delete(known, local)

  # A call can update booleans through aliases. Retain no constant fact across
  # one; compiler drop flags are re-established by explicit assignments.
  defp known_after(%{"Call" => _}, _, _), do: %{}
  defp known_after(%{"Assign" => _}, _, _), do: %{}

  defp known_after(_, known, _), do: known

  defp boolean(%{"Const" => constant}, _, ctx), do: constant_boolean(constant, ctx)

  defp boolean(%{"Copy" => %{"kind" => %{"Local" => local}}}, known, _),
    do: Map.get(known, local, :unknown)

  defp boolean(%{"Move" => %{"kind" => %{"Local" => local}}}, known, _),
    do: Map.get(known, local, :unknown)

  defp boolean(_, _, _), do: :unknown
  defp constant_boolean(%{"Value" => [_, [%{"Bool" => value}, _]]}, _), do: value
  defp constant_boolean(%{"Deduplicated" => id}, ctx), do: Map.get(ctx.booleans, id, :unknown)
  defp constant_boolean(_, _), do: :unknown

  # Constants have their own hash-cons family, separate from type IDs.
  defp boolean_constants(%{"Value" => [id, [%{"Bool" => value}, _]]}, found) do
    case Map.fetch(found, id) do
      {:ok, previous} when previous != value ->
        raise ArgumentError, "inconsistent native lifetime boolean constant identity"

      _ ->
        Map.put(found, id, value)
    end
  end

  defp boolean_constants(map, found) when is_map(map),
    do: boolean_constants(Map.values(map), found)

  defp boolean_constants(list, found) when is_list(list),
    do: Enum.reduce(list, found, &boolean_constants/2)

  defp boolean_constants(_, found), do: found

  defp statement!(%{"StorageLive" => _}, live, _), do: live

  defp statement!(%{"StorageDead" => local}, live, ctx) do
    if MapSet.member?(live, local), do: reject!(ctx)
    live
  end

  defp statement!(%{"Assign" => [dest, value]}, live, ctx) do
    if MapSet.size(live) > 0 and not (administrative?(value) or match?(%{"Ref" => _}, value)),
      do: reject!(ctx)

    transfer!(dest, value, live, ctx)
  end

  defp statement!(%{"Call" => %{"call" => call, "dest" => dest}}, live, ctx) do
    id = get_in(call, ["func", "Regular", "kind", "Fun"])
    model = ctx.models[id]
    remaining = moves!(call["args"], live, ctx)

    # Ownership can move into an actual extracted callee: its body is checked by
    # this same audit, and its effects compose through NativeM. No caller-owned
    # cell may remain live if that callee fails. External contracts cannot stand
    # in for a body here.
    if MapSet.size(live) > 0 and
         not ((MapSet.size(remaining) == 0 and
                 ((model && (model[:native_dispose] || model[:native_transfer])) ||
                    MapSet.member?(ctx.implementations, id))) or
                (MapSet.member?(ctx.nonpanicking, id) and
                   (MapSet.equal?(remaining, live) or (model && model[:native_dispose])))),
       do: reject!(ctx)

    destination!(dest, remaining, ctx)
  end

  defp statement!("Return", live, ctx) do
    if MapSet.size(MapSet.delete(live, 0)) > 0, do: reject!(ctx)
    :terminal
  end

  defp statement!(%{"Panic" => %{"on_unwind" => %{"statements" => []}}}, live, ctx) do
    if MapSet.size(live) > 0, do: reject!(ctx)
    :terminal
  end

  defp statement!(kind, live, ctx) do
    if MapSet.size(live) > 0 or nested_owner?(kind, ctx), do: reject!(ctx)
    live
  end

  defp administrative?(%{"Use" => _}), do: true
  defp administrative?(%{"Aggregate" => _}), do: true
  defp administrative?(_), do: false

  defp transfer!(dest, value, live, ctx) do
    remaining = moves!(value, live, ctx)

    if MapSet.size(remaining) < MapSet.size(live) and not nested_owner?(dest, ctx),
      do: reject!(ctx)

    destination!(dest, remaining, ctx)
  end

  defp destination!(%{"kind" => %{"Local" => local}}, live, ctx) do
    if MapSet.member?(ctx.owners, local) do
      if MapSet.member?(live, local), do: reject!(ctx)
      MapSet.put(live, local)
    else
      live
    end
  end

  defp destination!(dest, live, ctx) do
    if nested_owner?(dest, ctx), do: reject!(ctx)
    live
  end

  defp moves!(%{"Move" => %{"kind" => %{"Local" => local}}}, live, ctx) do
    if MapSet.member?(ctx.owners, local) and not MapSet.member?(live, local), do: reject!(ctx)
    MapSet.delete(live, local)
  end

  # A single-field variant moves its complete payload. Multi-field or opaque
  # containers cannot be partially consumed by this rule. All branch states
  # still undergo the same ownership and join checks.
  defp moves!(
         %{
           "Move" => %{
             "kind" => %{
               "Projection" => [
                 %{"kind" => %{"Local" => local}, "ty" => annotation},
                 %{"Field" => [variant, 0]}
               ]
             }
           }
         },
         live,
         ctx
       ) do
    if MapSet.member?(ctx.owners, local) do
      unless MapSet.member?(live, local), do: reject!(ctx)
      type = CallModels.expand(annotation, ctx.refs)
      unless type == ctx.locals[local], do: reject!(ctx)

      with %{"Adt" => %{"id" => id, "builtin" => nil}} <- type,
           %{"kind" => %{"Enum" => variants}} <- ctx.types[id],
           %{"fields" => [_]} <- Enum.find(variants, &(&1["id"] == variant)) do
        MapSet.delete(live, local)
      else
        _ -> reject!(ctx)
      end
    else
      live
    end
  end

  defp moves!(%{"Move" => place}, live, ctx) do
    if nested_owner?(place, ctx), do: reject!(ctx)
    live
  end

  defp moves!(%{"Copy" => place}, live, ctx) do
    if nested_owner?(place, ctx), do: reject!(ctx)
    live
  end

  defp moves!(map, live, ctx) when is_map(map), do: moves!(Map.values(map), live, ctx)

  defp moves!(list, live, ctx) when is_list(list),
    do: Enum.reduce(list, live, &moves!(&1, &2, ctx))

  defp moves!(_, live, _), do: live

  defp nested_owner?(%{"Local" => id}, ctx), do: MapSet.member?(ctx.owners, id)

  defp nested_owner?(map, ctx) when is_map(map),
    do: Enum.any?(Map.values(map), &nested_owner?(&1, ctx))

  defp nested_owner?(list, ctx) when is_list(list), do: Enum.any?(list, &nested_owner?(&1, ctx))
  defp nested_owner?(_, _), do: false

  defp reject!(ctx),
    do:
      LLBC.failure!(
        ctx.function,
        ctx.translated,
        "native owner lifetime requires unsupported unwind, partial moves or implicit cleanup; consume the owner before potentially failing operations"
      )
end
