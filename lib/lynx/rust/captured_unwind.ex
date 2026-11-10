defmodule Lynx.Rust.CapturedUnwind do
  @moduledoc false
  alias Lynx.Rust.{CallModels, DropModels, LLBC, LLBCJson, NativeBorrows}

  # Make exceptional exit explicit before Aeneas's ordinary borrow translation.
  # Err () means Rust panic after the actual MIR cleanup, never a successful Rust
  # return. Nonpanicking callees keep their original interfaces and actual bodies.
  def lower!(document, functions, refs) do
    translated = document["translated"]

    safe =
      NativeBorrows.nonpanicking_calls(functions, %{}, %{translated: translated, references: refs})

    lifted = Enum.reject(functions, &MapSet.member?(safe, &1["def_id"]))

    results =
      Enum.filter(
        translated["type_decls"],
        &(&1 && LLBC.result_type?(&1["def_id"], %{translated: translated, references: refs}))
      )

    result =
      case results do
        [result] ->
          result

        _ ->
          raise ArgumentError,
                "captured unwind requires the canonical core::result::Result definition"
      end

    unit = %{"Adt" => unit_adt()}
    next = max_id(document) + 1
    unit = %{"Value" => [next, unit]}

    {plans, _} =
      Enum.map_reduce(lifted, next + 1, fn function, next ->
        output = function["signature"]["output"]

        unless match?(%{"Structured" => _}, function["body"]) and
                 function["src"] == "Normal" and function["generics"]["types"] == [] and
                 function["generics"]["trait_clauses"] == [] and
                 (DropModels.primitive_scalar?(CallModels.expand(output, refs)) or
                    CallModels.expand(output, refs) == CallModels.expand(unit, refs)),
               do:
                 LLBC.failure!(
                   function,
                   translated,
                   "captured unwind requires a monomorphic ordinary function with scalar or unit output; fallible trait methods are unsupported"
                 )

        adt = %{
          "id" => result["def_id"],
          "generics" => arguments([output, unit]),
          "builtin" => nil
        }

        {{function["def_id"],
          %{output: output, type: %{"Value" => [next, %{"Adt" => adt}]}, adt: adt}}, next + 1}
      end)

    plans = Map.new(plans)

    {changed, {records, _}} =
      Enum.map_reduce(functions, {[], next + map_size(plans) + 1}, fn function, {records, next} ->
        if plan = plans[function["def_id"]] do
          body = function["body"]["Structured"]
          locals = body["locals"]["locals"]
          old = length(locals)

          state = %{
            function: function,
            translated: translated,
            safe: safe,
            plans: plans,
            plan: plan,
            unit: unit,
            owners: Enum.any?(locals, &owner?(CallModels.expand(&1["ty"], refs))),
            old: old,
            locals: locals ++ [Map.put(hd(locals), "index", old)],
            next: next
          }

          {block, state} = block(rename(body["body"], old), state, false)
          {live, state} = statement(hd(block["statements"]), %{"StorageLive" => 0}, state)
          block = update_in(block, ["statements"], &[live | &1])
          locals = List.update_at(state.locals, 0, &Map.put(&1, "ty", plan.type))

          changed =
            function
            |> put_in(["signature", "output"], plan.type)
            |> put_in(["body", "Structured", "body"], block)
            |> put_in(["body", "Structured", "locals", "locals"], locals)

          record = %{
            function_id: function["def_id"],
            original_signature: function["signature"],
            captured_signature: changed["signature"],
            panic: :result_err_unit,
            nonpanicking_dependencies: MapSet.to_list(safe) |> Enum.sort()
          }

          {changed, {[record | records], state.next}}
        else
          {function, {records, next}}
        end
      end)

    by_id = Map.new(changed, &{&1["def_id"], &1})

    document =
      update_in(document, ["translated", "fun_decls"], fn fs ->
        Enum.map(fs, fn f -> if f, do: Map.get(by_id, f["def_id"], f), else: nil end)
      end)

    document =
      document |> LLBCJson.restore_type_references!(document) |> LLBCJson.restore_spans!(document)

    {document, Enum.reverse(records)}
  end

  defp block(%{"statements" => statements} = block, state, cleanup) do
    {lists, state} = Enum.map_reduce(statements, state, &lower(&1, &2, cleanup))
    {Map.put(block, "statements", List.flatten(lists)), state}
  end

  defp lower(%{"kind" => "Return"} = s, state, false), do: finish(s, 0, state)
  defp lower(%{"kind" => "UnwindResume"} = s, state, true), do: finish(s, 1, state)

  defp lower(%{"kind" => %{"Panic" => %{"name" => name, "on_unwind" => cleanup}}}, state, false) do
    if is_nil(name), do: reject!(state, "captured panic is missing its compiler identity")
    panic!(name, state)

    if cleanup["statements"] == [],
      do: reject!(state, "captured panic is missing its unwind exit")

    {block, state} = block(cleanup, state, true)
    {block["statements"], state}
  end

  defp lower(
         %{
           "kind" => %{
             "Assert" => %{
               "assert" => assertion,
               "on_failure" => %{"Panic" => name},
               "on_unwind" => cleanup
             }
           }
         } = s,
         state,
         false
       ) do
    panic!(name, state)

    if state.owners,
      do:
        reject!(
          state,
          "captured unwind rejects reconstructed assertions with owned locals; original panic cleanup must be preserved"
        )

    {failure, state} = block(cleanup, state, true)

    {success, state} = new_block(s, [], state)
    branches = if assertion["expected"], do: [success, failure], else: [failure, success]

    {yes, state} = constant(%{"Bool" => true}, scalar_bool(), state)
    {no, state} = constant(%{"Bool" => false}, scalar_bool(), state)

    data = %{
      "scrutinee" => %{"Value" => assertion["cond"]},
      "branches" => [[yes, 0], [no, 1]],
      "fallback" => nil
    }

    {switch, state} =
      statement(s, %{"Switch" => %{"data" => data, "branches" => branches}}, state)

    {[switch], state}
  end

  defp lower(%{"kind" => %{"Call" => call}} = s, state, cleanup) do
    id = get_in(call, ["call", "func", "Regular", "kind", "Fun"])

    cond do
      MapSet.member?(state.safe, id) ->
        {call, state} = nonpanicking_call(s, call, state)
        {[call], state}

      plan = state.plans[id] ->
        if cleanup,
          do: reject!(state, "cleanup may panic again; native unwind termination is unsupported")

        {local, state} = local(plan.type, s, state)
        {live, state} = statement(s, %{"StorageLive" => local["kind"]["Local"]}, state)
        original = call["dest"]
        {invocation, state} = nonpanicking_call(s, Map.put(call, "dest", local), state)
        field = %{"kind" => %{"Projection" => [local, %{"Field" => [0, 0]}]}, "ty" => plan.output}

        {assign, state} =
          statement(s, %{"Assign" => [original, %{"Use" => [%{"Move" => field}, "Yes"]}]}, state)

        {failure, state} = block(call["on_unwind"], state, true)
        {zero, state} = constant(%{"Discriminant" => [plan.adt, 0]}, scalar_isize(), state)
        {one, state} = constant(%{"Discriminant" => [plan.adt, 1]}, scalar_isize(), state)

        data = %{
          "scrutinee" => %{"Discriminant" => local},
          "branches" => [[zero, 0], [one, 1]],
          "fallback" => nil
        }

        {success, state} = new_block(s, [assign], state)

        {switch, state} =
          statement(s, %{"Switch" => %{"data" => data, "branches" => [success, failure]}}, state)

        {[live, invocation, switch], state}

      true ->
        reject!(
          state,
          "captured unwind requires actual nonpanicking or captured first-party callees; external and indirect calls are unsupported"
        )
    end
  end

  defp lower(%{"kind" => %{"Switch" => switch}} = s, state, cleanup) do
    {branches, state} = Enum.map_reduce(switch["branches"], state, &block(&1, &2, cleanup))
    {[put_in(s, ["kind", "Switch", "branches"], branches)], state}
  end

  defp lower(%{"kind" => %{"Loop" => body}} = s, state, cleanup) do
    {body, state} = block(body, state, cleanup)
    {[put_in(s, ["kind", "Loop"], body)], state}
  end

  defp lower(%{"kind" => %{"Assign" => [_, value]}} = s, state, _) do
    unless safe_value?(value),
      do:
        reject!(
          state,
          "captured unwind rejects reconstructed fallible operations and unsupported assignments; original overflow/bounds cleanup edges are unavailable"
        )

    {[s], state}
  end

  defp lower(%{"kind" => kind} = s, state, _) when is_map(kind) do
    unless Enum.any?(~w(StorageLive StorageDead Break Continue), &Map.has_key?(kind, &1)),
      do: reject!(state, "unsupported captured unwind statement #{inspect(Map.keys(kind))}")

    {[s], state}
  end

  defp lower(%{"kind" => "Nop"} = s, state, _), do: {[s], state}

  defp lower(_, state, _),
    do:
      reject!(
        state,
        "unsupported captured unwind exit; termination and undefined behavior cannot be converted to a catchable panic"
      )

  defp safe_value?(%{"BinaryOp" => [op, _, _]}),
    do: op in ~w(BitAnd BitOr BitXor Eq Ne Lt Le Gt Ge)

  defp safe_value?(%{"UnaryOp" => ["Not", _]}), do: true

  defp safe_value?(value),
    do: Enum.any?(~w(Use Ref Aggregate Discriminant Len), &Map.has_key?(value, &1))

  defp nonpanicking_call(s, call, state) do
    {resume, state} = statement(s, "UnwindResume", state)
    edge = Map.put(call["on_unwind"], "statements", [resume])
    statement(s, %{"Call" => Map.put(call, "on_unwind", edge)}, state)
  end

  defp finish(s, variant, state) do
    {prefix, value, state} =
      if variant == 0 do
        {[], %{"Move" => %{"kind" => %{"Local" => state.old}, "ty" => state.plan.output}}, state}
      else
        {unit, state} = local(state.unit, s, state)
        {live, state} = statement(s, %{"StorageLive" => unit["kind"]["Local"]}, state)

        aggregate = %{
          "Aggregate" => [
            %{"Adt" => [unit_adt(), nil, nil]},
            []
          ]
        }

        {initialize, state} = statement(s, %{"Assign" => [unit, aggregate]}, state)
        {[live, initialize], %{"Move" => unit}, state}
      end

    dest = %{"kind" => %{"Local" => 0}, "ty" => state.plan.type}
    aggregate = %{"Aggregate" => [%{"Adt" => [state.plan.adt, variant, nil]}, [value]]}
    {assign, state} = statement(s, %{"Assign" => [dest, aggregate]}, state)
    {return, state} = statement(s, "Return", state)
    {prefix ++ [assign, return], state}
  end

  defp local(type, s, state) do
    id = length(state.locals)

    local = %{
      "index" => id,
      "name" => nil,
      "span" => s["span"],
      "ty" => type,
      "drop_flag_for" => nil
    }

    {%{"kind" => %{"Local" => id}, "ty" => type}, %{state | locals: state.locals ++ [local]}}
  end

  defp statement(s, kind, state),
    do: {%{s | "kind" => kind, "id" => state.next}, %{state | next: state.next + 1}}

  defp constant(kind, %{"Value" => _} = type, state),
    do: {%{"Value" => [state.next, [kind, type]]}, %{state | next: state.next + 1}}

  defp constant(kind, type, state),
    do: constant(kind, %{"Value" => [state.next, type]}, %{state | next: state.next + 1})

  defp new_block(s, statements, state),
    do:
      {%{"span" => s["span"], "id" => state.next, "statements" => statements},
       %{state | next: state.next + 1}}

  defp unit_adt, do: %{"id" => 0, "generics" => arguments([]), "builtin" => "Tuple"}
  defp scalar_bool, do: %{"Scalar" => "Bool"}
  defp scalar_isize, do: %{"Scalar" => %{"Integer" => %{"Signed" => "Isize"}}}

  defp arguments(types),
    do: %{"regions" => [], "types" => types, "const_generics" => [], "trait_refs" => []}

  defp owner?(%{"Ref" => _}), do: false
  defp owner?(%{"Adt" => %{"builtin" => "Tuple", "generics" => %{"types" => []}}}), do: false
  defp owner?(type), do: not DropModels.primitive_scalar?(type)

  defp reject!(state, reason), do: LLBC.failure!(state.function, state.translated, reason)

  defp panic!(nil, _), do: :ok

  defp panic!(
         [%{"Ident" => ["core", 0]}, %{"Ident" => ["panicking", 0]}, %{"Ident" => ["panic", 0]}],
         _
       ),
       do: :ok

  defp panic!(_, state),
    do:
      reject!(
        state,
        "captured unwind supports static-string panic only; generic or formatted panic payload behavior is unsupported"
      )

  defp rename(%{"Local" => 0}, id), do: %{"Local" => id}
  defp rename(%{"StorageLive" => 0}, id), do: %{"StorageLive" => id}
  defp rename(%{"StorageDead" => 0}, id), do: %{"StorageDead" => id}
  defp rename(map, id) when is_map(map), do: Map.new(map, fn {k, v} -> {k, rename(v, id)} end)
  defp rename(list, id) when is_list(list), do: Enum.map(list, &rename(&1, id))
  defp rename(value, _), do: value
  defp max_id(%{"Value" => [id, value]}), do: max(id, max_id(value))

  defp max_id(map) when is_map(map) do
    nested = map |> Map.values() |> Enum.map(&max_id/1) |> Enum.max(fn -> 0 end)
    if is_integer(map["id"]), do: max(nested, map["id"]), else: nested
  end

  defp max_id(list) when is_list(list), do: list |> Enum.map(&max_id/1) |> Enum.max(fn -> 0 end)
  defp max_id(_), do: 0
end
