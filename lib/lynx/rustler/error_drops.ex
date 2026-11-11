defmodule Lynx.Rustler.ErrorDrops do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Constants, DropModels, LLBC}
  @error Enum.map(~w(rustler error Error), &%{"Ident" => [&1, 0]})
  @name @error ++ [%{"Ident" => ["LynxDropDecoderError", 0]}]
  @scalars ~w(Bool U8 U16 U32 U64 U128 Usize I8 I16 I32 I64 I128 Isize)
  @args %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}

  # This is a partial destruction model, not a no-drop annotation on Error.
  # Boxed errors and unknown successful payloads exhaust verification. Only the SDK's
  # scalar/static-borrow error variants have successful no-effect transitions.
  def needed?(document, crates) do
    refs = LLBC.type_references!(document)
    translated = document["translated"]

    case Enum.find(translated["type_decls"], &(&1 && &1["item_meta"]["name"] == @error)) do
      nil ->
        false

      error ->
        Enum.any?(translated["fun_decls"], fn function ->
          function && first_party?(function, crates) &&
            result_drop?(function["body"], error["def_id"], translated, refs)
        end)
    end
  end

  defp result_drop?(%{"Drop" => %{"place" => %{"ty" => type}}}, error, translated, refs) do
    case CallModels.expand(type, refs) do
      %{"Adt" => %{"id" => result, "builtin" => nil, "generics" => %{"types" => [_, payload]}}} ->
        payload == %{"Adt" => %{"id" => error, "builtin" => nil, "generics" => @args}} &&
          LLBC.result_type?(result, %{translated: translated, references: refs})

      _ ->
        false
    end
  end

  defp result_drop?(map, error, translated, refs) when is_map(map),
    do: Enum.any?(Map.values(map), &result_drop?(&1, error, translated, refs))

  defp result_drop?(list, error, translated, refs) when is_list(list),
    do: Enum.any?(list, &result_drop?(&1, error, translated, refs))

  defp result_drop?(_, _, _, _), do: false

  def lower!(document, layout, crates) do
    document = Lynx.Rust.LLBCJson.restore_constant_references!(document, document)
    refs = LLBC.type_references!(document)
    translated = document["translated"]
    error = Enum.find(translated["type_decls"], &(&1 && &1["item_meta"]["name"] == @error))

    full =
      Enum.find(layout["translated"]["type_decls"], &(&1 && &1["item_meta"]["name"] == @error))

    if "rustler" in crates, do: raise(ArgumentError, "cannot model first-party Rustler drops")
    # Constructor lowering validates the actual field layouts before this pass.
    unless error && error["kind"] == "Opaque" && full &&
             Enum.map(full["kind"]["Enum"], & &1["name"]) ==
               ~w(BadArg Atom RaiseAtom RaiseTerm Term),
           do: raise(ArgumentError, "unsupported compiled Rustler Error drop layout")

    full_refs = LLBC.type_references!(layout)
    [badarg, atom, raise_atom | _] = full["kind"]["Enum"]

    unless badarg["id"] == 0 and badarg["fields"] == [] and
             Enum.all?([{atom, 1}, {raise_atom, 2}], fn {variant, id} ->
               case variant["fields"] do
                 [%{"is_positional" => true, "ty" => type}] ->
                   variant["id"] == id and
                     Lynx.Rustler.ErrorLiterals.static_string?(type, full_refs)

                 _ ->
                   false
               end
             end) and full["item_meta"]["has_errors"] == false and
             Enum.all?(Map.values(full["generics"]), &(&1 == [])),
           do: raise(ArgumentError, "unsupported compiled Rustler Error drop fields")

    functions = translated["fun_decls"]

    reserved =
      [@name, @error ++ [%{"Ident" => ["LynxDropErrResult", 0]}]] ++
        Enum.map(@scalars, fn scalar ->
          @error ++ [%{"Ident" => ["LynxDropScalarResult" <> scalar, 0]}]
        end)

    if Enum.any?(functions, &(&1 && &1["item_meta"]["name"] in reserved)),
      do: raise(ArgumentError, "Rustler error drop primitive identity collision")

    state = %{
      refs: refs,
      translated: translated,
      error: error,
      sites: [],
      declarations: %{},
      function_id: length(functions),
      next: max_id(document) + 1,
      reference: Enum.max(Map.keys(refs), fn -> -1 end) + 1
    }

    {functions, state} =
      Enum.map_reduce(functions, state, fn function, state ->
        if function && first_party?(function, crates) && is_map(function["body"]) do
          state = Map.put(state, :locals, function["body"]["Structured"]["locals"]["locals"])
          {body, state} = walk(function["body"]["Structured"]["body"], state, function)
          function = put_in(function, ["body", "Structured", "body"], body)
          function = put_in(function, ["body", "Structured", "locals", "locals"], state.locals)
          {function, state}
        else
          {function, state}
        end
      end)

    if state.sites == [] do
      {document, nil}
    else
      declarations = state.declarations |> Map.values() |> Enum.sort_by(& &1["def_id"])
      order = translated["ordered_decls"]
      position = Enum.find_index(order, &(&1 == %{"Type" => %{"NonRec" => error["def_id"]}}))
      if position == nil, do: raise(ArgumentError, "missing Rustler Error declaration order")

      document =
        document
        |> put_in(["translated", "fun_decls"], functions ++ declarations)
        |> update_in(
          ["translated", "item_names"],
          &(&1 ++
              Enum.map(declarations, fn d ->
                %{"key" => %{"Fun" => d["def_id"]}, "value" => d["item_meta"]["name"]}
              end))
        )
        |> put_in(
          ["translated", "ordered_decls"],
          Enum.take(order, position + 1) ++
            Enum.map(declarations, &%{"Fun" => %{"NonRec" => &1["def_id"]}}) ++
            Enum.drop(order, position + 1)
        )

      {document, %{declarations: state.declarations, sites: Enum.reverse(state.sites)}}
    end
  end

  def models!(_document, nil), do: %{}

  def models!(document, proof) do
    Map.new(proof.declarations, fn {mode, declaration} ->
      id = declaration["def_id"]

      unless Enum.at(document["translated"]["fun_decls"], id) == declaration,
        do: raise(ArgumentError, "missing or inconsistent validated Rustler error drop primitive")

      suffix =
        case mode do
          :error -> "dropDecoderError"
          {:scalar_result, scalar} -> "dropScalarResult" <> scalar
          :result -> "dropErrResult"
        end

      name = List.last(declaration["item_meta"]["name"])["Ident"] |> hd()

      {id,
       %{
         rust_name: "rustler::error::Error::" <> name,
         lean: "Lynx.Rustler.Decoding." <> suffix,
         builtin: false,
         can_fail: true,
         lift: false,
         function: declaration,
         definition_id: id,
         status: :modelled,
         implementation_verified: false,
         label:
           "Validated compiler Result drop with opaque Rustler Error: BadArg/Atom/RaiseAtom errors complete; " <>
             if(match?({:scalar_result, _}, mode),
               do: "compiler-validated scalar Ok payloads complete without effects; ",
               else: "unknown Ok payloads exhaust verification; "
             ) <>
             "boxed errors exhaust verification; compiler glue, SDK, allocator and native FFI unverified"
       }}
    end)
  end

  # The compiler has already branched around a possibly moved Ok payload.
  # Only rewrite the one-statement Err arm of that exact cleanup switch. No
  # path fact is propagated past assignments, calls or arbitrary statements.
  defp walk_cleanup(
         %{"kind" => %{"Switch" => %{"data" => data, "branches" => branches} = switch}} =
           statement,
         state,
         function
       ) do
    with %{"Discriminant" => place} <- data["scrutinee"],
         %{"Adt" => %{"id" => result, "builtin" => nil} = adt} <-
           CallModels.expand(place["ty"], state.refs),
         true <-
           LLBC.result_type?(result, %{translated: state.translated, references: state.refs}),
         [[%{"Value" => [_, [%{"Discriminant" => [constant_adt, 0]}, constant_type]]}, 0]] <-
           data["branches"],
         true <- CallModels.expand(%{"Adt" => constant_adt}, state.refs) == %{"Adt" => adt},
         true <-
           CallModels.expand(constant_type, state.refs) == %{
             "Scalar" => %{"Integer" => %{"Signed" => "Isize"}}
           },
         1 <- data["fallback"],
         [ok, %{"statements" => [%{"kind" => %{"Drop" => drop}} = drop_statement]} = err] <-
           branches,
         true <- drop["place"] == place do
      {ok, state} = walk(ok, state, function)
      {changed, state} = lower_drop(drop_statement, state, function, :error)
      err = %{err | "statements" => [changed]}
      {%{statement | "kind" => %{"Switch" => %{switch | "branches" => [ok, err]}}}, state}
    else
      _ -> children(statement, state, function)
    end
  end

  defp walk(%{"kind" => %{"Drop" => _}} = statement, state, function),
    do: lower_drop(statement, state, function, :result)

  defp walk(
         %{"kind" => %{"Switch" => %{"data" => data, "branches" => branches} = switch}} =
           statement,
         state,
         function
       ) do
    with %{"Discriminant" => %{"kind" => %{"Local" => local}} = place} <- data["scrutinee"],
         %{"Adt" => %{"id" => result} = adt} <- CallModels.expand(place["ty"], state.refs),
         true <-
           LLBC.result_type?(result, %{translated: state.translated, references: state.refs}),
         true <- data["fallback"] == nil and length(branches) == 2,
         [[ok, 0], [err, 1]] <- data["branches"],
         true <- discriminant?(ok, adt, 0, state) and discriminant?(err, adt, 1, state),
         false <- borrows_local?(function["body"], local) do
      {branches, state} =
        Enum.map_reduce(Enum.with_index(branches), state, fn {branch, variant}, state ->
          {statements, {state, _}} =
            Enum.map_reduce(branch["statements"], {state, true}, fn stmt, {state, preserved} ->
              case cleanup_drop(stmt, place, adt, state) do
                {:ok, drop} when preserved ->
                  if variant == 0 do
                    {[], {state, true}}
                  else
                    {changed, state} = lower_drop(drop, state, function, :error)
                    {[changed], {state, true}}
                  end

                _ ->
                  {changed, state} = walk(stmt, state, function)
                  {[changed], {state, preserved and not changes_tag?(stmt, local)}}
              end
            end)

          {%{branch | "statements" => List.flatten(statements)}, state}
        end)

      {%{statement | "kind" => %{"Switch" => %{switch | "branches" => branches}}}, state}
    else
      _ -> walk_cleanup(statement, state, function)
    end
  end

  defp walk(value, state, function), do: children(value, state, function)

  defp lower_drop(%{"kind" => %{"Drop" => drop}} = statement, state, function, mode) do
    case CallModels.expand(drop["place"]["ty"], state.refs) do
      %{
        "Adt" => %{
          "id" => result,
          "builtin" => nil,
          "generics" => %{"types" => [_, error]} = args
        }
      } ->
        expected = %{
          "Adt" => %{"id" => state.error["def_id"], "builtin" => nil, "generics" => @args}
        }

        if error == expected && Constants.empty_arguments?(%{args | "types" => []}) &&
             LLBC.result_type?(result, %{translated: state.translated, references: state.refs}) do
          glue = DropModels.validate_result_glue!(drop, function, state.translated, state.refs)
          [payload, error_type] = drop["fn_ptr"]["generics"]["types"]

          scalar_type = CallModels.expand(payload, state.refs)

          mode =
            if mode == :result and DropModels.primitive_scalar?(scalar_type),
              do: {:scalar_result, scalar_name(scalar_type)},
              else: mode

          state = declaration(state, result, mode)
          declaration = state.declarations[mode]

          error_place = %{
            "kind" => %{"Projection" => [drop["place"], %{"Field" => [1, 0]}]},
            "ty" => error_type
          }

          local = length(state.locals)
          unit = declaration["signature"]["output"]
          dest = %{"kind" => %{"Local" => local}, "ty" => unit}

          locals =
            state.locals ++
              [
                %{
                  "index" => local,
                  "name" => nil,
                  "span" => statement["span"],
                  "ty" => unit,
                  "drop_flag_for" => nil
                }
              ]

          # Successful supported errors cannot unwind. Unsupported payloads
          # fail with verification exhaustion, never a fabricated Rust panic.
          resume = %{
            "span" => statement["span"],
            "id" => state.next + 1,
            "kind" => "UnwindResume",
            "comments_before" => []
          }

          call = %{
            "call" => %{
              "func" => %{
                "Regular" => %{
                  "kind" => %{"Fun" => declaration["def_id"]},
                  "generics" =>
                    if(mode in [:error] or match?({:scalar_result, _}, mode),
                      do: @args,
                      else: %{@args | "types" => [payload]}
                    )
                }
              },
              "args" => [%{"Move" => if(mode == :error, do: error_place, else: drop["place"])}],
              "safety" => "Inherit"
            },
            "dest" => dest,
            "on_unwind" => %{
              "span" => statement["span"],
              "id" => state.next,
              "statements" => [resume]
            }
          }

          site = %{
            caller: function["def_id"],
            statement: statement["id"],
            span: statement["span"],
            compiler_drop: glue.id,
            mode: mode
          }

          {%{statement | "kind" => %{"Call" => call}},
           %{state | locals: locals, next: state.next + 2, sites: [site | state.sites]}}
        else
          children(statement, state, function)
        end

      _ ->
        children(statement, state, function)
    end
  end

  defp discriminant?(
         %{"Value" => [_, [%{"Discriminant" => [actual, variant]}, type]]},
         adt,
         variant,
         state
       ),
       do:
         CallModels.expand(%{"Adt" => actual}, state.refs) == %{"Adt" => adt} and
           CallModels.expand(type, state.refs) == %{
             "Scalar" => %{"Integer" => %{"Signed" => "Isize"}}
           }

  defp discriminant?(_, _, _, _), do: false

  defp cleanup_drop(
         %{"kind" => %{"Switch" => %{"data" => data, "branches" => [ok, err]}}},
         place,
         adt,
         state
       ) do
    with %{"Discriminant" => ^place} <- data["scrutinee"],
         [[constant, 0]] <- data["branches"],
         true <- discriminant?(constant, adt, 0, state),
         1 <- data["fallback"],
         [] <- ok["statements"],
         [%{"kind" => %{"Drop" => %{"place" => ^place}}} = drop] <- err["statements"],
         do: {:ok, drop},
         else: (_ -> :no)
  end

  defp cleanup_drop(_, _, _, _), do: :no

  defp borrows_local?(%{"Ref" => %{"place" => place}}, local), do: rooted?(place, local)
  defp borrows_local?(%{"RawPtr" => %{"place" => place}}, local), do: rooted?(place, local)

  defp borrows_local?(map, local) when is_map(map),
    do: Enum.any?(Map.values(map), &borrows_local?(&1, local))

  defp borrows_local?(list, local) when is_list(list),
    do: Enum.any?(list, &borrows_local?(&1, local))

  defp borrows_local?(_, _), do: false

  defp changes_tag?(%{"dest" => %{"kind" => %{"Local" => local}}}, local), do: true

  defp changes_tag?(%{"SetDiscriminant" => [%{"kind" => %{"Local" => local}}, _]}, local),
    do: true

  defp changes_tag?(%{"StorageLive" => local}, local), do: true
  defp changes_tag?(%{"Assign" => [%{"kind" => %{"Local" => local}}, _]}, local), do: true
  defp changes_tag?(%{"Move" => %{"kind" => %{"Local" => local}}}, local), do: true
  defp changes_tag?(%{"StorageDead" => local}, local), do: true
  defp changes_tag?(%{"Drop" => %{"place" => %{"kind" => %{"Local" => local}}}}, local), do: true

  defp changes_tag?(map, local) when is_map(map),
    do: Enum.any?(Map.values(map), &changes_tag?(&1, local))

  defp changes_tag?(list, local) when is_list(list), do: Enum.any?(list, &changes_tag?(&1, local))
  defp changes_tag?(_, _), do: false
  defp rooted?(%{"kind" => %{"Local" => local}}, local), do: true
  defp rooted?(%{"kind" => %{"Projection" => [parent, _]}}, local), do: rooted?(parent, local)
  defp rooted?(_, _), do: false

  defp children(map, state, function) when is_map(map) do
    {pairs, state} =
      Enum.map_reduce(map, state, fn {k, v}, state ->
        {v, state} = walk(v, state, function)
        {{k, v}, state}
      end)

    {Map.new(pairs), state}
  end

  defp children(list, state, function) when is_list(list),
    do: Enum.map_reduce(list, state, &walk(&1, &2, function))

  defp children(value, state, _), do: {value, state}

  defp declaration(state, result, mode) do
    if state.declarations[mode] do
      state
    else
      r = state.reference

      input = %{
        "Value" => [
          r,
          %{"Adt" => %{"id" => state.error["def_id"], "builtin" => nil, "generics" => @args}}
        ]
      }

      unit = %{
        "Value" => [r + 1, %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => @args}}]
      }

      params = Map.new(state.error["generics"], fn {k, _} -> {k, []} end)

      {input, params, name} =
        if mode == :error do
          {input, params, @name}
        else
          scalar =
            case mode do
              {:scalar_result, scalar} -> scalar
              _ -> nil
            end

          type = %{
            "Value" => [
              r + 2,
              if(scalar, do: scalar_type(scalar), else: %{"TypeVar" => %{"Free" => 0}})
            ]
          }

          result_type = %{
            "Value" => [
              r + 3,
              %{
                "Adt" => %{
                  "id" => result,
                  "builtin" => nil,
                  "generics" => %{@args | "types" => [type, input]}
                }
              }
            ]
          }

          {result_type,
           if(scalar,
             do: params,
             else:
               Map.put(params, "types", [
                 %{"index" => 0, "name" => "T", "variance" => "Invariant"}
               ])
           ),
           @error ++
             [
               %{
                 "Ident" => [
                   if(scalar, do: "LynxDropScalarResult" <> scalar, else: "LynxDropErrResult"),
                   0
                 ]
               }
             ]}
        end

      decl = %{
        "def_id" => state.function_id + map_size(state.declarations),
        "src" => "Normal",
        "body" => "Opaque",
        "item_meta" =>
          Map.merge(state.error["item_meta"], %{"name" => name, "opacity" => "Opaque"}),
        "generics" => params,
        "signature" => %{
          "is_unsafe" => false,
          "abi" => "Rust",
          "is_variadic" => false,
          "inputs" => [input],
          "output" => unit
        }
      }

      %{state | declarations: Map.put(state.declarations, mode, decl), reference: r + 4}
    end
  end

  defp scalar_name(%{"Scalar" => "Bool"}), do: "Bool"
  defp scalar_name(%{"Scalar" => %{"Integer" => integer}}), do: integer |> Map.values() |> hd()
  defp scalar_type("Bool"), do: %{"Scalar" => "Bool"}
  defp scalar_type("U" <> _ = scalar), do: %{"Scalar" => %{"Integer" => %{"Unsigned" => scalar}}}
  defp scalar_type("I" <> _ = scalar), do: %{"Scalar" => %{"Integer" => %{"Signed" => scalar}}}

  defp first_party?(%{"item_meta" => %{"name" => [%{"Ident" => [crate, _]} | _]}}, crates),
    do: crate in crates

  defp first_party?(_, _), do: false

  defp max_id(map) when is_map(map),
    do:
      max(
        if(is_integer(map["id"]), do: map["id"], else: 0),
        Enum.max(Enum.map(Map.values(map), &max_id/1), fn -> 0 end)
      )

  defp max_id(list) when is_list(list), do: Enum.max(Enum.map(list, &max_id/1), fn -> 0 end)
  defp max_id(_), do: 0
end
