defmodule Lynx.Rust.NativeBorrows do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, LockModels}

  # The backend returns reconstructed mutable borrows only on success. Until
  # failure outputs are supported, a borrowed guard must not be lost on panic.
  # Check actual callee bodies transitively, rather than trusting a contract.
  def audit!(functions, models, translated, refs) do
    guards =
      for type <- translated["type_decls"], LockModels.guard?(type, refs), do: type["def_id"]

    types =
      for type <- translated["type_decls"],
          type != nil,
          into: %{},
          do: {type["def_id"], CallModels.expand(type["kind"], refs)}

    context = %{guards: guards, types: types}
    implementations = Map.new(functions, &{&1["def_id"], &1})

    for function <- functions,
        borrowed_guard?(CallModels.expand(function["signature"]["inputs"], refs), context),
        not total?(function["def_id"], implementations, models, []) do
      LLBC.failure!(
        function,
        translated,
        "borrowed native guard requires nonpanicking, terminating implementation dependencies; mutable-borrow outputs on failure are unsupported"
      )
    end
  end

  defp borrowed_guard?(%{"Ref" => [_, type, _]}, guards), do: contains_guard?(type, guards)

  defp borrowed_guard?(map, guards) when is_map(map),
    do: Enum.any?(Map.values(map), &borrowed_guard?(&1, guards))

  defp borrowed_guard?(list, guards) when is_list(list),
    do: Enum.any?(list, &borrowed_guard?(&1, guards))

  defp borrowed_guard?(_, _), do: false

  defp contains_guard?(type, context), do: contains_guard?(type, context, [])

  defp contains_guard?(%{"Adt" => %{"id" => id}} = type, ctx, seen) do
    id in ctx.guards or
      Enum.any?(Map.values(type), &contains_guard?(&1, ctx, seen)) or
      (id not in seen and contains_guard?(ctx.types[id], ctx, [id | seen]))
  end

  defp contains_guard?(map, ctx, seen) when is_map(map),
    do: Enum.any?(Map.values(map), &contains_guard?(&1, ctx, seen))

  defp contains_guard?(list, ctx, seen) when is_list(list),
    do: Enum.any?(list, &contains_guard?(&1, ctx, seen))

  defp contains_guard?(_, _, _), do: false

  defp total?(id, functions, models, seen) do
    cond do
      id in seen ->
        false

      model = models[id] ->
        model.can_fail == false

      function = functions[id] ->
        case function["body"] do
          %{"Structured" => %{"body" => body}} -> block?(body, functions, models, [id | seen])
          _ -> false
        end

      true ->
        false
    end
  end

  defp block?(%{"statements" => statements}, functions, models, seen),
    do: Enum.all?(statements, &statement?(&1["kind"], functions, models, seen))

  defp block?(_, _, _, _), do: false
  defp statement?("Return", _, _, _), do: true
  defp statement?(%{"StorageLive" => _}, _, _, _), do: true
  defp statement?(%{"StorageDead" => _}, _, _, _), do: true

  defp statement?(%{"Assign" => [_, value]}, _, _, _),
    do: Enum.any?(~w(Use Ref Aggregate Discriminant Len), &Map.has_key?(value, &1))

  defp statement?(%{"Switch" => %{"branches" => branches}}, functions, models, seen),
    do: Enum.all?(branches, &block?(&1, functions, models, seen))

  defp statement?(%{"Call" => %{"call" => call}}, functions, models, seen) do
    case get_in(call, ["func", "Regular", "kind"]) do
      %{"Fun" => id} -> total?(id, functions, models, seen)
      _ -> false
    end
  end

  defp statement?(_, _, _, _), do: false
end
