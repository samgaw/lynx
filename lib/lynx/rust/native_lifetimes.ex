defmodule Lynx.Rust.NativeLifetimes do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC, MutexModels, LockModels}

  # Track consuming ownership on every branch. Potential failure with a live
  # owner requires supported cleanup; borrowed calls need checked nonpanicking
  # bodies. Whole single-field enum payloads may transfer their ownership.
  def audit!(functions, models, translated, refs) do
    native_types =
      for type <- translated["type_decls"],
          type &&
            (MutexModels.type?(type) or LockModels.guard?(type, refs) or
               Lynx.Rust.ResourceModels.type?(type) or
               (Lynx.Rust.FileModels.file_type?(translated, type["def_id"]) and
                  Enum.any?(models, fn {_, model} -> model[:native_file_drop] == true end)) or
               (Lynx.Rust.FileModels.error_type?(translated, type["def_id"]) and
                  Enum.any?(models, fn {_, model} -> model[:native_io_error_drop] == true end))),
          do: type["def_id"]

    types = Map.new(Enum.reject(translated["type_decls"], &is_nil/1), &{&1["def_id"], &1})
    coroutines = coroutine_storage!(types, translated, refs)

    types =
      Map.new(types, fn {id, type} ->
        {id, Map.put(type, :native_coroutine_storage, coroutines[id])}
      end)

    frame_inputs =
      for function <- functions,
          coroutine_entry?(function, "poll"),
          %{"Structured" => body} <- [function["body"]],
          into: %{} do
        inputs =
          for {input, index} <- Enum.with_index(function["signature"]["inputs"], 1),
              type = CallModels.expand(input, refs),
              %{borrowed: true} = frame <- [frame_info(type, types, refs, coroutines, [])],
              local = Enum.find(body["locals"]["locals"], &(&1["index"] == index)),
              local != nil,
              frame ==
                frame_info(CallModels.expand(local["ty"], refs), types, refs, coroutines, []),
              do: index

        {function["def_id"], inputs}
      end

    # These bodies are audited below: panic with a live frame owner is rejected.
    # A consuming caller may therefore retain that same sole frame across its
    # compiler poll, even though repolling an empty completed frame may panic.
    # Verification cutoffs do not establish a Rust outcome or cleanup guarantee.
    preserving_polls =
      for function <- functions,
          coroutine_entry?(function, "poll"),
          %{"Structured" => _} <- [function["body"]],
          [input, _context] <- [function["signature"]["inputs"]],
          %{borrowed: true, id: id} <- [
            frame_info(CallModels.expand(input, refs), types, refs, coroutines, [])
          ],
          into: %{},
          do: {function["def_id"], id}

    # Compiler poll entries are checked below by state-sensitive ownership
    # analysis. Their completed-state panic cannot lose a live saved guard.
    Lynx.Rust.NativeBorrows.audit!(functions, models, translated, refs, frame_inputs)
    implementations = MapSet.new(functions, & &1["def_id"])

    nonpanicking =
      Lynx.Rust.NativeBorrows.nonpanicking_calls(functions, models, %{
        translated: translated,
        references: refs
      })

    for function <- functions,
        %{"Structured" => body} <- [function["body"]] do
      owners =
        for local <- body["locals"]["locals"],
            contains_native?(CallModels.expand(local["ty"], refs), native_types, types, refs, []),
            into: MapSet.new(),
            do: local["index"]

      frames =
        for local <- body["locals"]["locals"],
            local["index"] > 0 and local["index"] <= body["locals"]["arg_count"],
            frame = frame_info(CallModels.expand(local["ty"], refs), types, refs, coroutines, []),
            frame != nil,
            into: %{},
            do: {local["index"], frame}

      borrowed = MapSet.new(for {id, frame} <- frames, frame.borrowed, do: id)

      if MapSet.size(borrowed) > 0 and not coroutine_entry?(function, "poll"),
        do:
          LLBC.failure!(
            function,
            translated,
            "borrowed owned-future state currently requires the compiler poll entry"
          )

      owners = MapSet.union(owners, borrowed)

      if MapSet.size(owners) > 0 do
        live = MapSet.filter(owners, &(&1 > 0 and &1 <= body["locals"]["arg_count"]))

        context = %{
          owners: owners,
          borrowed: borrowed,
          frames: frames,
          native: native_types,
          coroutines: coroutines,
          cutoff_undefined: get_in(translated, ["options", "cancelling_futures"]) == true,
          models: models,
          implementations: implementations,
          nonpanicking: nonpanicking,
          preserving_polls: preserving_polls,
          function: function,
          translated: translated,
          types: types,
          refs: refs,
          locals:
            Map.new(body["locals"]["locals"], &{&1["index"], CallModels.expand(&1["ty"], refs)}),
          booleans: boolean_constants(translated, %{}),
          discriminants: discriminant_constants(translated, %{})
        }

        unless block!(body["body"], live, context) == :terminal, do: reject!(context)
      end
    end
  end

  # Inspect actual fields after instantiation. A Pin containing a mutable
  # reference borrows its pointee; its type argument alone does not own it.
  defp contains_native?(type, native, types, refs, seen),
    do: native_count(type, native, types, refs, seen) > 0

  defp native_count(%{"Ref" => _}, _, _, _, _), do: 0

  defp native_count(
         %{"Adt" => %{"id" => id, "builtin" => builtin, "generics" => args}},
         native,
         types,
         refs,
         seen
       ) do
    cond do
      id in native and is_nil(builtin) ->
        1

      builtin == "Tuple" ->
        Enum.sum(Enum.map(args["types"], &native_count(&1, native, types, refs, seen)))

      id in seen ->
        0

      match?(%{"Alias" => _}, types[id]["kind"]) ->
        native_count(
          CallModels.instantiate(CallModels.expand(types[id]["kind"]["Alias"], refs), args),
          native,
          types,
          refs,
          [id | seen]
        )

      # Validated frame slots are state alternatives: a transferred capture and
      # its saved slot do not represent two simultaneously live native owners.
      metadata = types[id][:native_coroutine_storage] ->
        metadata["states"]
        |> Enum.map(fn indices ->
          Enum.sum(
            for index <- indices do
              field = Enum.at(metadata["fields"], index)

              native_count(
                CallModels.instantiate(CallModels.expand(field["ty"], refs), args),
                native,
                types,
                refs,
                [id | seen]
              )
            end
          )
        end)
        |> Enum.max(fn -> 0 end)

      is_map(types[id]["kind"]) ->
        kind = types[id]["kind"]

        counts =
          for fields <-
                (case kind do
                   %{"Struct" => fields} -> [fields]
                   %{"Enum" => variants} -> Enum.map(variants, & &1["fields"])
                   _ -> []
                 end) do
            Enum.sum(
              for field <- fields,
                  do:
                    native_count(
                      CallModels.instantiate(CallModels.expand(field["ty"], refs), args),
                      native,
                      types,
                      refs,
                      [id | seen]
                    )
            )
          end

        Enum.max(counts, fn -> 0 end)

      true ->
        Enum.sum(Enum.map(args["types"], &native_count(&1, native, types, refs, seen)))
    end
  end

  defp native_count(%{"Array" => [type | _]}, native, types, refs, seen),
    do: if(native_count(type, native, types, refs, seen) > 0, do: 2, else: 0)

  defp native_count(map, native, types, refs, seen) when is_map(map),
    do: Enum.sum(Enum.map(Map.values(map), &native_count(&1, native, types, refs, seen)))

  defp native_count(list, native, types, refs, seen) when is_list(list),
    do: Enum.sum(Enum.map(list, &native_count(&1, native, types, refs, seen)))

  defp native_count(_, _, _, _, _), do: 0

  defp coroutine_entry?(item, method) do
    name = item["item_meta"]["name"]

    length(name) >= 3 and Enum.at(name, -2) == %{"Builtin" => ["Closure", 0]} and
      List.last(name) == %{"Ident" => [method, 0]}
  end

  defp coroutine_storage!(types, translated, refs) do
    for {id, type} <- types,
        attribute <- type["item_meta"]["attr_info"]["attributes"] || [],
        %{"Unknown" => %{"path" => path, "args" => args}} <- [attribute],
        path in ["lynx::coroutine_storage_v1", "lynx::coroutine_storage_v2"],
        into: %{} do
      metadata = JSON.decode!(args)

      unless type["src"] == "Normal" and
               List.last(type["item_meta"]["name"]) == %{"Builtin" => ["Closure", 0]} and
               match?(%{"Struct" => _}, type["kind"]) and
               Enum.sort(Map.keys(metadata)) == ~w(state states) and
               is_integer(metadata["state"]) and is_list(metadata["states"]) and
               length(metadata["states"]) >= 3 and
               Enum.slice(metadata["states"], 1, 2) == [[], []] and
               if(path == "lynx::coroutine_storage_v2",
                 do:
                   metadata["state"] > 0 and
                     hd(metadata["states"]) == Enum.to_list(0..(metadata["state"] - 1)),
                 else: hd(metadata["states"]) == []
               ),
             do: LLBC.failure!(type, translated, "invalid compiler coroutine storage evidence")

      fields = type["kind"]["Struct"]

      unless Enum.count(type["item_meta"]["attr_info"]["attributes"], fn attribute ->
               match?(
                 %{"Unknown" => %{"path" => path}}
                 when path in ["lynx::coroutine_storage_v1", "lynx::coroutine_storage_v2"],
                 attribute
               )
             end) == 1,
             do: LLBC.failure!(type, translated, "duplicate compiler coroutine storage evidence")

      unless metadata["state"] >= 0 and metadata["state"] < length(fields) and
               Enum.all?(Enum.with_index(metadata["states"]), fn {indices, tag} ->
                 is_list(indices) and Enum.uniq(indices) == indices and
                   Enum.all?(
                     indices,
                     &(is_integer(&1) and &1 >= 0 and &1 < length(fields) and
                         if(tag == 0 and path == "lynx::coroutine_storage_v2",
                           do: &1 < metadata["state"],
                           else: &1 > metadata["state"]
                         ))
                   )
               end),
             do: LLBC.failure!(type, translated, "invalid compiler coroutine saved-field mapping")

      unless CallModels.expand(Enum.at(fields, metadata["state"])["ty"], refs) ==
               %{"Scalar" => %{"Integer" => %{"Unsigned" => "U32"}}},
             do: LLBC.failure!(type, translated, "invalid compiler coroutine state type")

      {id, Map.put(metadata, "fields", fields)}
    end
  end

  defp frame_info(type, types, refs, coros, path, seen \\ [])

  defp frame_info(%{"Ref" => [_, type, "Mut"]}, types, refs, coros, path, seen) do
    case frame_info(type, types, refs, coros, path ++ [:deref], seen) do
      nil -> nil
      info -> %{info | borrowed: true}
    end
  end

  defp frame_info(%{"Ref" => _}, _, _, _, _, _), do: nil

  defp frame_info(
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}},
         types,
         refs,
         coros,
         path,
         seen
       ) do
    cond do
      coros[id] ->
        %{id: id, prefix: path, borrowed: false, args: args, wrappers: []}

      id in seen ->
        nil

      match?(%{"Struct" => [_]}, types[id]["kind"]) ->
        [field] = types[id]["kind"]["Struct"]
        type = CallModels.instantiate(CallModels.expand(field["ty"], refs), args)

        case frame_info(type, types, refs, coros, path ++ [{:field, nil, 0}], [id | seen]) do
          nil -> nil
          info -> %{info | wrappers: [id | info.wrappers]}
        end

      true ->
        nil
    end
  end

  defp frame_info(_, _, _, _, _, _), do: nil

  defp resolve_place(%{"kind" => %{"Local" => root}}, _known), do: {root, []}

  defp resolve_place(%{"kind" => %{"Projection" => [parent, step]}}, known) do
    {root, path} = resolve_place(parent, known)

    case {step, path, known[{:alias, root}]} do
      {"Deref", [], {alias, prefix}} ->
        {alias, prefix}

      {"Deref", [{:field, nil, 0}], _} ->
        case known[{:frame_borrow, root}] do
          {owner, _id, prefix} -> {owner, prefix}
          _ -> {root, path ++ [:deref]}
        end

      {"Deref", _, _} ->
        {root, path ++ [:deref]}

      {%{"Field" => [variant, index]}, _, _} ->
        {root, path ++ [{:field, variant, index}]}

      _ ->
        {root, path ++ [:unsupported]}
    end
  end

  defp resolve_place(_, _), do: {nil, []}

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
          case statement!(kind, state.live, Map.put(ctx, :known, state.known)) do
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
        Enum.with_index(branches)
        |> Enum.map(fn {branch, index} ->
          block_state!(
            branch,
            refine_coroutine(data, index, refine_enum(data, index, state, ctx), ctx),
            ctx
          )
        end)
        |> Enum.reject(&(&1 == :terminal))

      case states do
        [] ->
          :terminal

        [first | rest] ->
          unless Enum.all?(
                   rest,
                   &MapSet.equal?(
                     MapSet.difference(MapSet.delete(&1.live, 0), ctx.borrowed),
                     MapSet.difference(MapSet.delete(first.live, 0), ctx.borrowed)
                   )
                 ),
                 do: reject!(ctx)

          # Return variants may contain different native owners. Keep the union
          # for subsequent failure checks; only Return may finally transfer slot 0.
          # Every other local still requires identical ownership at the join.
          live = Enum.reduce(rest, first.live, &MapSet.union(&1.live, &2))

          known =
            Map.filter(first.known, fn {id, value} ->
              Enum.all?(rest, &(&1.known[id] == value))
            end)

          %{first | known: known, live: live}
      end
    end
  end

  # A Result error (or another empty enum variant) does not own the native
  # payload of its alternative. Derive this from the actual instantiated fields
  # and compiler discriminants, never from a constructor name or annotation alone.
  defp refine_enum(
         %{"scrutinee" => %{"Discriminant" => %{"kind" => %{"Local" => root}} = place}} = data,
         index,
         state,
         ctx
       ) do
    if MapSet.member?(ctx.owners, root) and not MapSet.member?(ctx.borrowed, root) do
      type = Lynx.Rust.NativeDropLowering.place_type!(place, ctx, true)

      with %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <- type,
           %{"kind" => %{"Enum" => variants}} <- ctx.types[id] do
        declared = Enum.map(variants, & &1["id"])

        branches =
          Enum.map(data["branches"], fn [constant, branch] ->
            {actual, variant} = discriminant_constant!(constant, ctx)

            unless Lynx.Rust.NativeDropLowering.same_runtime_type?(actual, type) and
                     variant in declared,
                   do: reject!(ctx)

            {variant, branch}
          end)

        tags = Enum.map(branches, &elem(&1, 0))

        unless length(Enum.uniq(tags)) == length(tags) and
                 (data["fallback"] != nil or Enum.sort(tags) == Enum.sort(declared)),
               do: reject!(ctx)

        selected = for {variant, branch} <- branches, branch == index, do: variant

        selected =
          if data["fallback"] == index,
            do: selected ++ (declared -- Enum.map(branches, &elem(&1, 0))),
            else: selected

        if selected == [] do
          state
        else
          owned =
            Enum.any?(variants, fn variant ->
              variant["id"] in selected and
                Enum.any?(variant["fields"], fn field ->
                  contains_native?(
                    CallModels.instantiate(CallModels.expand(field["ty"], ctx.refs), args),
                    ctx.native,
                    ctx.types,
                    ctx.refs,
                    []
                  )
                end)
            end)

          if owned do
            unless MapSet.member?(state.live, root), do: reject!(ctx)
            state
          else
            %{
              state
              | live: MapSet.delete(state.live, root),
                known: Map.put(state.known, {:empty, root}, true)
            }
          end
        end
      else
        _ -> state
      end
    else
      state
    end
  end

  defp refine_enum(_, _, state, _), do: state

  defp discriminant_constant!(%{"Value" => [_, [%{"Discriminant" => [type, variant]}, _]]}, ctx),
    do: {CallModels.expand(%{"Adt" => type}, ctx.refs), variant}

  defp discriminant_constant!(%{"Deduplicated" => id}, ctx) do
    case ctx.discriminants[id] do
      nil -> reject!(ctx)
      constant -> discriminant_constant!(constant, ctx)
    end
  end

  defp discriminant_constant!(_, ctx), do: reject!(ctx)

  defp discriminant_constants(%{"Value" => [id, [%{"Discriminant" => _}, _]]} = value, found) do
    case Map.fetch(found, id) do
      {:ok, previous} when previous != value ->
        raise ArgumentError, "inconsistent native enum discriminant identity"

      _ ->
        Map.put(found, id, value)
    end
  end

  defp discriminant_constants(map, found) when is_map(map),
    do: discriminant_constants(Map.values(map), found)

  defp discriminant_constants(list, found) when is_list(list),
    do: Enum.reduce(list, found, &discriminant_constants/2)

  defp discriminant_constants(_, found), do: found

  defp refine_coroutine(data, index, state, ctx) do
    fact =
      case data["scrutinee"] do
        %{"Value" => operand} -> state_operand(operand, state.known, ctx)
        _ -> nil
      end

    case fact do
      {:coroutine_state, root} ->
        frame = ctx.frames[root]

        tags =
          for [constant, branch] <- data["branches"],
              branch == index,
              do: scalar_constant(constant, ctx)

        tags =
          if data["fallback"] == index do
            explicit =
              Enum.map(data["branches"], fn [constant, _] -> scalar_constant(constant, ctx) end)

            case state.known[{:states, root}] do
              domain when is_list(domain) ->
                if Enum.all?(explicit, &is_integer/1), do: tags ++ (domain -- explicit), else: []

              _ ->
                []
            end
          else
            tags
          end

        if tags != [] and Enum.all?(tags, &is_integer/1) do
          metadata = ctx.coroutines[frame.id]

          owned =
            Enum.any?(tags, fn tag ->
              case Enum.fetch(metadata["states"], tag) do
                {:ok, indices} ->
                  Enum.any?(indices, fn field ->
                    type =
                      CallModels.instantiate(
                        CallModels.expand(Enum.at(metadata["fields"], field)["ty"], ctx.refs),
                        frame.args
                      )

                    contains_native?(type, ctx.native, ctx.types, ctx.refs, [])
                  end)

                _ ->
                  true
              end
            end)

          %{
            state
            | known: Map.put(state.known, {:states, root}, tags),
              live:
                if(owned, do: MapSet.put(state.live, root), else: MapSet.delete(state.live, root))
          }
        else
          state
        end

      _ ->
        state
    end
  end

  defp state_operand(%{"Move" => %{"kind" => %{"Local" => id}}}, known, _), do: known[id]

  defp state_operand(%{"Copy" => place}, known, ctx) do
    {root, path} = resolve_place(place, known)

    if ctx.frames[root] &&
         path ==
           ctx.frames[root].prefix ++
             [{:field, nil, ctx.coroutines[ctx.frames[root].id]["state"]}] do
      {:coroutine_state, root}
    else
      case place do
        %{"kind" => %{"Local" => id}} -> known[id]
        _ -> nil
      end
    end
  end

  defp state_operand(_, _, _), do: nil

  defp scalar_constant(
         %{"Value" => [_, [%{"Integer" => %{"Unsigned" => ["U32", value]}}, _]]},
         _
       ),
       do: parse_state(value)

  defp scalar_constant(%{"Deduplicated" => id}, ctx), do: Map.get(ctx.booleans, id, :unknown)
  defp scalar_constant(_, _), do: :unknown

  defp parse_state(value) when is_binary(value) do
    case Integer.parse(value) do
      {n, ""} when n >= 0 and n < 4_294_967_296 -> n
      _ -> :unknown
    end
  end

  defp parse_state(_), do: :unknown

  defp known_after(%{"Assign" => [%{"kind" => %{"Local" => local}}, value]}, known, ctx) do
    known =
      known
      |> Map.delete({:alias, local})
      |> Map.delete({:empty, local})
      |> Map.delete({:frame_borrow, local})

    known =
      if empty_value?(value, known, ctx), do: Map.put(known, {:empty, local}, true), else: known

    case value do
      %{"Aggregate" => [_kind, [%{"Move" => place}]]} ->
        target = frame_info(ctx.locals[local], ctx.types, ctx.refs, ctx.coroutines, [])

        case {target, Lynx.Rust.NativeDropLowering.place_type!(place, ctx, true)} do
          {%{borrowed: true, id: id, prefix: [{:field, nil, 0}, :deref]},
           %{"Ref" => [_, pointee, "Mut"]}} ->
            {root, path} = resolve_place(%{"kind" => %{"Projection" => [place, "Deref"]}}, known)
            owned = frame_info(ctx.locals[root], ctx.types, ctx.refs, ctx.coroutines, [])

            if match?(%{borrowed: false, id: ^id, prefix: ^path}, owned) and
                 match?(
                   %{borrowed: false, id: ^id, prefix: []},
                   frame_info(pointee, ctx.types, ctx.refs, ctx.coroutines, [])
                 ) and
                 native_count(ctx.locals[root], ctx.native, ctx.types, ctx.refs, []) == 1,
               do: Map.put(Map.delete(known, local), {:frame_borrow, local}, {root, id, path}),
               else: Map.delete(known, local)

          _ ->
            Map.delete(known, local)
        end

      %{"Ref" => %{"place" => place}} ->
        Map.put(Map.delete(known, local), {:alias, local}, resolve_place(place, known))

      %{"Use" => [%{"Copy" => place}, _]} ->
        {root, path} = resolve_place(place, known)

        if ctx.frames[root] &&
             path ==
               ctx.frames[root].prefix ++
                 [{:field, nil, ctx.coroutines[ctx.frames[root].id]["state"]}],
           do: Map.put(known, local, {:coroutine_state, root}),
           else: known_boolean(local, boolean(%{"Copy" => place}, known, ctx), known)

      %{"Use" => [%{"Move" => %{"kind" => %{"Local" => source}}} = operand, _]} ->
        case {known[{:frame_borrow, source}],
              frame_info(ctx.locals[local], ctx.types, ctx.refs, ctx.coroutines, [])} do
          {{root, id, path}, %{borrowed: true, id: id}} ->
            known
            |> Map.delete({:frame_borrow, source})
            |> Map.put({:frame_borrow, local}, {root, id, path})

          _ ->
            known_boolean(local, boolean(operand, known, ctx), known)
        end

      %{"Use" => [operand, _]} ->
        known_boolean(local, boolean(operand, known, ctx), known)

      _ ->
        Map.delete(known, local)
    end
  end

  defp known_after(%{"StorageDead" => local}, known, _),
    do:
      known
      |> Map.delete(local)
      |> Map.delete({:alias, local})
      |> Map.delete({:empty, local})
      |> Map.delete({:frame_borrow, local})

  # A compiler poll mutates the frame, not the address held by another Pin
  # reborrow. Retain only aliases of that same audited frame, never state tags
  # or ownership-emptiness facts learned before the call.
  defp known_after(
         %{
           "Call" => %{
             "call" => %{
               "func" => %{"Regular" => %{"kind" => %{"Fun" => callee}}},
               "args" => [%{"Move" => %{"kind" => %{"Local" => pin}}}, _]
             }
           }
         },
         known,
         ctx
       ) do
    frame = known[{:frame_borrow, pin}]

    case {ctx.preserving_polls[callee], frame} do
      {id, {_root, id, _path}} when is_integer(id) ->
        Map.filter(known, fn {key, value} ->
          match?({:alias, _}, key) or (match?({:frame_borrow, _}, key) and value == frame)
        end)

      _ ->
        Map.filter(known, fn {key, _} -> match?({:alias, _}, key) end)
    end
  end

  defp known_after(%{"Call" => _}, known, _),
    do: Map.filter(known, fn {key, _} -> match?({:alias, _}, key) end)

  defp known_after(%{"Assign" => _}, known, _),
    do: Map.filter(known, fn {key, _} -> match?({:alias, _}, key) end)

  defp known_after(_, known, _), do: known

  defp empty_value?(%{"Aggregate" => [_kind, operands]}, known, ctx),
    do: Enum.all?(operands, &empty_operand?(&1, known, ctx))

  defp empty_value?(%{"Use" => [operand, _]}, known, ctx), do: empty_operand?(operand, known, ctx)
  defp empty_value?(_, _, _), do: false

  defp empty_operand?(operand, known, ctx) when is_map(operand) do
    case operand do
      %{"Move" => %{"kind" => %{"Local" => local}, "ty" => type}} ->
        not contains_native?(
          CallModels.expand(type, ctx.refs),
          ctx.native,
          ctx.types,
          ctx.refs,
          []
        ) or known[{:empty, local}] == true

      %{"Copy" => %{"kind" => %{"Local" => local}, "ty" => type}} ->
        not contains_native?(
          CallModels.expand(type, ctx.refs),
          ctx.native,
          ctx.types,
          ctx.refs,
          []
        ) or known[{:empty, local}] == true

      %{"Const" => _} ->
        true

      _ ->
        false
    end
  end

  defp empty_operand?(_, _, _), do: false

  defp known_boolean(local, value, known),
    do: if(is_boolean(value), do: Map.put(known, local, value), else: Map.delete(known, local))

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

  defp boolean_constants(
         %{"Value" => [id, [%{"Integer" => %{"Unsigned" => ["U32", value]}}, _]]},
         found
       ),
       do: Map.put(found, id, parse_state(value))

  defp boolean_constants(map, found) when is_map(map),
    do: boolean_constants(Map.values(map), found)

  defp boolean_constants(list, found) when is_list(list),
    do: Enum.reduce(list, found, &boolean_constants/2)

  defp boolean_constants(_, found), do: found

  defp statement!(%{"StorageLive" => _}, live, _), do: live

  defp statement!(%{"StorageDead" => local}, live, ctx) do
    if MapSet.member?(live, local) and not MapSet.member?(ctx.borrowed, local), do: reject!(ctx)
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

    remaining =
      if model && model[:native_replace],
        do: replace_owner!(call, live, ctx),
        else: moves!(call["args"], live, ctx)

    # Ownership can move into an actual extracted callee: its body is checked by
    # this same audit, and its effects compose through NativeM. No caller-owned
    # cell may remain live if that callee fails. The separate compiler-frame rule
    # allows only that same sole frame: its audited panic states have no native
    # owner. External contracts cannot stand in for a body here.
    if MapSet.size(live) > 0 and
         !((MapSet.size(remaining) == 0 and
              ((model && (model[:native_dispose] || model[:native_transfer])) ||
                 MapSet.member?(ctx.implementations, id))) or
             preserving_poll_borrow?(call, live, remaining, ctx) or
             (MapSet.member?(ctx.nonpanicking, id) and
                (MapSet.equal?(remaining, live) or
                   MapSet.member?(ctx.implementations, id) or
                   (model && (model[:native_dispose] || model[:native_replace]))))),
       do: reject!(ctx)

    destination!(dest, remaining, ctx)
  end

  defp statement!("Return", live, ctx) do
    if MapSet.size(MapSet.difference(MapSet.delete(live, 0), ctx.borrowed)) > 0, do: reject!(ctx)
    :terminal
  end

  defp statement!(%{"Panic" => %{"on_unwind" => %{"statements" => cleanup}}}, live, ctx) do
    if MapSet.size(live) > 0, do: reject!(ctx)

    unless Enum.all?(cleanup, fn statement ->
             case statement["kind"] do
               %{"StorageDead" => _} -> true
               terminal when terminal in ["UnwindResume", "UnwindTerminate"] -> true
               _ -> false
             end
           end),
           do: reject!(ctx)

    :terminal
  end

  defp statement!("UndefinedBehavior", _live, %{cutoff_undefined: true}), do: :terminal

  defp statement!(kind, live, ctx) do
    if MapSet.size(live) > 0 or nested_owner?(kind, ctx), do: reject!(ctx)
    live
  end

  defp preserving_poll_borrow?(
         %{
           "func" => %{"Regular" => %{"kind" => %{"Fun" => id}}},
           "args" => [%{"Move" => %{"kind" => %{"Local" => pin}}}, _]
         },
         live,
         remaining,
         ctx
       ) do
    case {ctx.preserving_polls[id], ctx.known[{:frame_borrow, pin}], MapSet.to_list(live)} do
      {id, {root, id, _path}, [root]} when is_integer(id) -> MapSet.equal?(live, remaining)
      _ -> false
    end
  end

  defp preserving_poll_borrow?(_, _, _, _), do: false

  # Only an empty replacement can transfer the one saved owner out of a frame.
  # Non-owning replacements retain the ordinary call path.
  defp replace_owner!(%{"args" => [borrow, replacement]}, live, ctx) do
    place =
      case borrow do
        %{"Move" => place} -> place
        %{"Copy" => place} -> place
        _ -> reject!(ctx)
      end

    case Lynx.Rust.NativeDropLowering.place_type!(place, ctx, true) do
      %{"Ref" => [_, type, "Mut"]} ->
        {root, path} = resolve_place(%{"kind" => %{"Projection" => [place, "Deref"]}}, ctx.known)

        if contains_native?(type, ctx.native, ctx.types, ctx.refs, []) do
          frame = ctx.frames[root]

          frame_type =
            if frame,
              do: %{"Adt" => %{"id" => frame.id, "builtin" => nil, "generics" => frame.args}}

          unless frame && path != [] && MapSet.member?(live, root) &&
                   native_count(frame_type, ctx.native, ctx.types, ctx.refs, []) == 1 &&
                   native_count(type, ctx.native, ctx.types, ctx.refs, []) == 1 &&
                   empty_operand?(replacement, ctx.known, ctx),
                 do: reject!(ctx)

          MapSet.delete(live, root)
        else
          moves!([borrow, replacement], live, ctx)
        end

      _ ->
        reject!(ctx)
    end
  end

  defp administrative?(%{"Use" => _}), do: true
  defp administrative?(%{"Aggregate" => _}), do: true
  defp administrative?(%{"Discriminant" => _}), do: true
  defp administrative?(_), do: false

  defp transfer!(dest, value, live, ctx) do
    remaining = moves!(value, live, ctx)
    transferred = MapSet.size(remaining) < MapSet.size(live)
    if transferred and not native_place?(dest, ctx), do: reject!(ctx)
    if transferred, do: destination!(dest, remaining, ctx), else: remaining
  end

  defp native_place?(place, ctx),
    do:
      contains_native?(
        Lynx.Rust.NativeDropLowering.place_type!(place, ctx, true),
        ctx.native,
        ctx.types,
        ctx.refs,
        []
      )

  defp destination!(%{"kind" => %{"Local" => local}} = place, live, ctx) do
    Lynx.Rust.NativeDropLowering.place_type!(place, ctx, true)

    if MapSet.member?(ctx.owners, local) do
      if MapSet.member?(live, local), do: reject!(ctx)
      MapSet.put(live, local)
    else
      live
    end
  end

  defp destination!(dest, live, ctx) do
    if native_place?(dest, ctx) do
      {root, _} = resolve_place(dest, ctx.known)

      unless ctx.frames[root] && ctx.frames[root].borrowed &&
               native_count(ctx.locals[root], ctx.native, ctx.types, ctx.refs, []) == 0,
             do: reject!(ctx)

      if MapSet.member?(live, root), do: reject!(ctx)
      MapSet.put(live, root)
    else
      live
    end
  end

  defp moves!(%{"Move" => %{"kind" => %{"Local" => local}} = place}, live, ctx) do
    Lynx.Rust.NativeDropLowering.place_type!(place, ctx, true)

    if MapSet.member?(ctx.owners, local) and not MapSet.member?(live, local) and
         ctx.known[{:empty, local}] != true,
       do: reject!(ctx)

    MapSet.delete(live, local)
  end

  # A projection can transfer the complete native ownership of a container only
  # when the actual instantiated type contains exactly one native owner.
  defp moves!(%{"Move" => place}, live, ctx) do
    if native_place?(place, ctx) do
      {root, _} = resolve_place(place, ctx.known)

      unless MapSet.member?(live, root),
        do:
          LLBC.failure!(
            ctx.function,
            ctx.translated,
            "native owner lifetime: projected native field is uninitialized or consumed"
          )

      root_type =
        if ctx.frames[root],
          do: %{
            "Adt" => %{
              "id" => ctx.frames[root].id,
              "builtin" => nil,
              "generics" => ctx.frames[root].args
            }
          },
          else: ctx.locals[root]

      unless native_count(root_type, ctx.native, ctx.types, ctx.refs, []) == 1, do: reject!(ctx)
      MapSet.delete(live, root)
    else
      live
    end
  end

  defp moves!(%{"Copy" => place}, live, ctx) do
    if native_place?(place, ctx), do: reject!(ctx)
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
