defmodule Lynx.Rust.NativeLifetimes do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, MutexModels}

  # Extraction can reconstruct assertions without their unwind drops. Logical
  # heap ownership still needs cleanup. Until unwind is interpreted, admit only
  # straight-line owner lifetimes without a potentially failing intervening step.
  def audit!(functions, models, translated, refs) do
    mutexes =
      for type <- translated["type_decls"], type && MutexModels.type?(type), do: type["def_id"]

    types = Map.new(Enum.reject(translated["type_decls"], &is_nil/1), &{&1["def_id"], &1})
    implementations = MapSet.new(functions, & &1["def_id"])

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
          function: function,
          translated: translated
        }

        block!(body["body"], live, context)
      end
    end
  end

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

  defp block!(%{"statements" => statements}, live, ctx),
    do: Enum.reduce(statements, live, &statement!(&1["kind"], &2, ctx))

  defp statement!(%{"StorageLive" => _}, live, _), do: live

  defp statement!(%{"StorageDead" => local}, live, ctx) do
    if MapSet.member?(live, local), do: reject!(ctx)
    live
  end

  defp statement!(%{"Assign" => [dest, value]}, live, ctx) do
    if MapSet.size(live) > 0 and not administrative?(value), do: reject!(ctx)
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
         not (MapSet.size(remaining) == 0 and
                ((model && model[:native_dispose]) || MapSet.member?(ctx.implementations, id))),
       do: reject!(ctx)

    destination!(dest, remaining, ctx)
  end

  defp statement!("Return", live, ctx) do
    if MapSet.size(MapSet.delete(live, 0)) > 0, do: reject!(ctx)
    live
  end

  defp statement!(%{"Switch" => %{"branches" => branches}}, live, ctx) do
    if MapSet.size(live) > 0, do: reject!(ctx)
    Enum.reduce(branches, live, &MapSet.union(&2, block!(&1, live, ctx)))
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
        "native owner lifetime requires unsupported unwind, branching or implicit cleanup; consume the owner before potentially failing operations"
      )
end
