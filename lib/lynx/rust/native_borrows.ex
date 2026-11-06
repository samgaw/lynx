defmodule Lynx.Rust.NativeBorrows do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, LockModels, MutexModels}

  # The backend returns reconstructed mutable borrows only on success. Until
  # failure outputs are supported, a borrowed guard must not be lost on panic.
  # Check actual callee bodies transitively, rather than trusting a contract.
  def audit!(functions, models, translated, refs, frame_inputs \\ %{}) do
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
        {input, index} <- Enum.with_index(function["signature"]["inputs"], 1),
        borrowed_guard?(CallModels.expand(input, refs), context),
        index not in Map.get(frame_inputs, function["def_id"], []),
        not nonpanicking?(function["def_id"], implementations, models, []) do
      LLBC.failure!(
        function,
        translated,
        "borrowed native guard requires nonpanicking implementation dependencies; mutable-borrow outputs on failure are unsupported"
      )
    end
  end

  def nonpanicking_calls(functions, models) do
    by_id = Map.new(functions, &{&1["def_id"], &1})

    MapSet.new(
      for id <- Map.keys(by_id) ++ Map.keys(models), nonpanicking?(id, by_id, models, []), do: id
    )
  end

  # Compiler cleanup after a certified nonpanicking call is unreachable. Keep
  # the original LLBC and a call-site record; never erase a potentially panicking call's drops.
  def prune_owned_calls!(document, first_party, enabled_models \\ []) do
    translated = document["translated"]
    refs = LLBC.type_references!(document)
    all = Enum.reject(translated["fun_decls"], &is_nil/1)

    {functions, external} =
      Enum.split_with(all, fn function ->
        case hd(function["item_meta"]["name"]) do
          %{"Ident" => [crate, _]} -> crate in first_party
          _ -> false
        end
      end)

    {helpers, external} =
      Enum.split_with(external, &Lynx.Rust.LibraryHelpers.selected?(&1, translated))

    models = CallModels.resolve(external, translated, refs, enabled_models, :runtime)

    case Lynx.Rust.NativeDrops.audit(functions, models, translated, refs) do
      :ok -> :ok
      {:error, function, message} -> LLBC.failure!(function, translated, message)
    end

    safe = nonpanicking_calls(functions ++ helpers, models)

    owners =
      for type <- translated["type_decls"],
          type &&
            (LockModels.guard?(type, refs) or MutexModels.type?(type) or
               Lynx.Rust.ResourceModels.type?(type)),
          do: type["def_id"]

    {all, records} =
      Enum.map_reduce(all, [], fn function, records ->
        owned =
          case function["body"] do
            %{"Structured" => %{"locals" => %{"locals" => locals}}} ->
              Enum.any?(locals, fn local ->
                case CallModels.expand(local["ty"], refs) do
                  %{"Adt" => %{"id" => id}} -> id in owners
                  _ -> false
                end
              end)

            _ ->
              false
          end

        if owned and Enum.any?(functions, &(&1["def_id"] == function["def_id"])) do
          {body, records} = prune(function["body"], safe, function["def_id"], models, records)
          {Map.put(function, "body", body), records}
        else
          {function, records}
        end
      end)

    {put_in(
       document,
       ["translated", "fun_decls"],
       Enum.map(translated["fun_decls"], fn
         nil -> nil
         function -> Enum.find(all, &(&1["def_id"] == function["def_id"]))
       end)
     ), Enum.reverse(records)}
  end

  defp prune(
         %{"kind" => %{"Call" => %{"call" => call, "on_unwind" => cleanup}}} = statement,
         safe,
         caller,
         models,
         records
       ) do
    id = get_in(call, ["func", "Regular", "kind", "Fun"])

    if MapSet.member?(safe, id) and cleanup["statements"] != [] do
      kind =
        if models[id] && models[id][:native_dispose],
          do: :nonpanicking_drop_call,
          else: :nonpanicking_borrow_call

      record = %{
        kind: kind,
        caller: caller,
        statement: statement["id"],
        function: id,
        cleanup_block: cleanup["id"]
      }

      statement = put_in(statement, ["kind", "Call", "on_unwind", "statements"], [])
      prune_children(statement, safe, caller, models, [record | records])
    else
      prune_children(statement, safe, caller, models, records)
    end
  end

  defp prune(value, safe, caller, models, records),
    do: prune_children(value, safe, caller, models, records)

  defp prune_children(map, safe, caller, models, records) when is_map(map) do
    {pairs, records} =
      Enum.map_reduce(Enum.sort(map), records, fn {key, value}, records ->
        {value, records} = prune(value, safe, caller, models, records)
        {{key, value}, records}
      end)

    {Map.new(pairs), records}
  end

  defp prune_children(list, safe, caller, models, records) when is_list(list),
    do: Enum.map_reduce(list, records, &prune(&1, safe, caller, models, &2))

  defp prune_children(value, _, _, _, records), do: {value, records}

  defp borrowed_guard?(%{"Ref" => [_, type, _]}, guards), do: contains_guard?(type, guards)

  defp borrowed_guard?(%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}}, ctx) do
    seen = Map.get(ctx, :borrowed_seen, [])

    if id in seen do
      false
    else
      ctx = Map.put(ctx, :borrowed_seen, [id | seen])

      case ctx.types[id] do
        %{"Struct" => fields} ->
          Enum.any?(fields, &borrowed_guard?(CallModels.instantiate(&1["ty"], args), ctx))

        %{"Enum" => variants} ->
          Enum.any?(variants, fn v ->
            Enum.any?(v["fields"], &borrowed_guard?(CallModels.instantiate(&1["ty"], args), ctx))
          end)

        %{"Alias" => type} ->
          borrowed_guard?(CallModels.instantiate(type, args), ctx)

        _ ->
          Enum.any?(args["types"], &borrowed_guard?(&1, ctx))
      end
    end
  end

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

  defp nonpanicking?(id, functions, models, seen) do
    cond do
      id in seen ->
        false

      model = models[id] ->
        # These validated native models can block or exhaust verification, but
        # cannot raise a catchable Rust panic. Their failure cannot justify a
        # successful proof or unwind into a stale reconstructed mutable borrow.
        model.can_fail == false or model[:native_cutoff_only] == true

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

  # Primitive bitwise operations cannot overflow or panic. Overloaded Rust
  # operators are calls and still require their actual nonpanicking bodies.
  defp statement?(%{"Assign" => [_, %{"BinaryOp" => [op, _, _]}]}, _, _, _)
       when op in ~w(BitAnd BitOr BitXor), do: true

  defp statement?(%{"Assign" => [_, value]}, _, _, _),
    do: Enum.any?(~w(Use Ref Aggregate Discriminant Len), &Map.has_key?(value, &1))

  defp statement?(%{"Switch" => %{"branches" => branches}}, functions, models, seen),
    do: Enum.all?(branches, &block?(&1, functions, models, seen))

  defp statement?(%{"Call" => %{"call" => call}}, functions, models, seen) do
    case get_in(call, ["func", "Regular", "kind"]) do
      %{"Fun" => id} -> nonpanicking?(id, functions, models, seen)
      _ -> false
    end
  end

  defp statement?(_, _, _, _), do: false
end
