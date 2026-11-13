defmodule Lynx.Rustler.ValueConstructors do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Constants, LLBC, LLBCJson}
  alias Lynx.Rustler.ErrorLiterals
  @error Enum.map(~w(rustler error Error), &%{"Ident" => [&1, 0]})
  @args %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}

  def lower!(document, layout, crates) do
    error =
      Enum.find(document["translated"]["type_decls"], &(&1 && &1["item_meta"]["name"] == @error))

    full =
      Enum.find(layout["translated"]["type_decls"], &(&1 && &1["item_meta"]["name"] == @error))

    refs = LLBC.type_references!(document)
    variants = variants!(full, layout)
    funs = document["translated"]["fun_decls"]

    initial = %{
      document: document,
      refs: refs,
      layout: layout,
      full: full,
      types: document["translated"]["type_decls"],
      globals:
        LLBCJson.restore_global_constant_values!(
          Enum.reject(document["translated"]["global_decls"] || [], &is_nil/1),
          document
        ),
      error: error,
      variants: variants,
      entries: [],
      sites: [],
      next: max_id(document) + 1,
      first_id: length(funs),
      reference: Enum.max(Map.keys(refs), fn -> -1 end) + 1
    }

    {funs, state} =
      Enum.map_reduce(funs, initial, fn function, state ->
        if function && first_party?(function, crates) do
          {body, state} = walk(function["body"], state, function)
          {%{function | "body" => body}, state}
        else
          {function, state}
        end
      end)

    if state.entries == [] do
      {document, nil}
    else
      names = Enum.map(funs, fn f -> f && f["item_meta"]["name"] end)

      for entry <- state.entries,
          entry.declaration["item_meta"]["name"] in names,
          do: raise(ArgumentError, "Rustler atom constructor primitive identity collision")

      order = document["translated"]["ordered_decls"]
      position = Enum.find_index(order, &(&1 == %{"Type" => %{"NonRec" => error["def_id"]}}))

      if position == nil,
        do: raise(ArgumentError, "missing compiled Rustler Error declaration order")

      declarations = Enum.map(state.entries, & &1.declaration)
      entries = Enum.map(state.entries, &%{"Fun" => %{"NonRec" => &1.declaration["def_id"]}})

      doc =
        document
        |> put_in(["translated", "fun_decls"], funs ++ declarations)
        |> put_in(
          ["translated", "ordered_decls"],
          Enum.take(order, position + 1) ++ entries ++ Enum.drop(order, position + 1)
        )
        |> update_in(["translated", "item_names"], fn names ->
          names ++
            Enum.map(
              declarations,
              &%{"key" => %{"Fun" => &1["def_id"]}, "value" => &1["item_meta"]["name"]}
            )
        end)

      # Later cleanup preparation expands shared references. Close only the new
      # foreign declarations now, so their exact identity receipts survive that
      # representation change. Leave original implementation bodies untouched.
      closed =
        doc
        |> LLBCJson.restore_type_references!(doc)
        |> LLBCJson.restore_spans!(doc)

      entries =
        Enum.map(state.entries, fn entry ->
          declaration = Enum.at(closed["translated"]["fun_decls"], entry.declaration["def_id"])
          %{entry | declaration: declaration}
        end)

      doc =
        Enum.reduce(entries, doc, fn entry, doc ->
          update_in(doc, ["translated", "fun_decls"], fn functions ->
            List.replace_at(functions, entry.declaration["def_id"], entry.declaration)
          end)
        end)

      {doc, %{entries: entries, sites: Enum.reverse(state.sites)}}
    end
  end

  defp variants!(full, layout) do
    refs = LLBC.type_references!(layout)

    literals =
      for name <- ~w(Atom RaiseAtom), into: %{} do
        variants = full["kind"]["Enum"]

        case Enum.filter(variants, &(&1["name"] == name)) do
          [%{"id" => id, "fields" => [%{"is_positional" => true, "ty" => type}]} = variant]
          when is_integer(id) and id >= 0 ->
            unless Enum.at(variants, id) == variant && ErrorLiterals.static_string?(type, refs),
              do:
                raise(
                  ArgumentError,
                  "inconsistent compiled Rustler #{name} variant or string field"
                )

            {id, name}

          _ ->
            raise ArgumentError, "missing compiled Rustler #{name} string constructor"
        end
      end

    payloads =
      for variant <- full["kind"]["Enum"],
          variant["name"] in ~w(Term RaiseTerm),
          into: %{},
          do: {variant["id"], variant["name"]}

    Map.merge(literals, payloads)
  end

  defp payload_operation([%{"Move" => %{"ty" => type}} = operand], name, state) do
    variants = state.full["kind"]["Enum"]

    case Enum.filter(variants, &(&1["name"] == name)) do
      [%{"id" => id, "fields" => [%{"is_positional" => true, "ty" => field}]} = variant] ->
        full_refs = LLBC.type_references!(state.layout)

        if Enum.at(variants, id) == variant &&
             boxed_encoder?(field, state.layout, full_refs, :static) &&
             boxed_encoder?(type, state.document, state.refs, :local),
           do: {:ok, %{literal: nil, inputs: [type], arguments: [operand]}},
           else: :error

      _ ->
        :error
    end
  end

  defp payload_operation(_, _, _), do: :error

  defp boxed_encoder?(type, document, refs, lifetime) do
    with %{"Adt" => %{"id" => box, "builtin" => "Box", "generics" => args}} <-
           CallModels.expand(type, refs),
         [dyn] <- args["types"],
         true <- Constants.empty_arguments?(%{args | "types" => []}),
         [%{"item_meta" => %{"name" => name}}] <-
           Enum.filter(document["translated"]["type_decls"], &(&1 && &1["def_id"] == box)),
         true <- name == Enum.map(~w(alloc boxed Box), &%{"Ident" => [&1, 0]}),
         %{
           "DynTrait" => %{
             "binder" => %{
               "kind" => "Dyn",
               "skip_binder" => %{"TypeVar" => %{"Bound" => [0, 0]}},
               "params" => params
             }
           }
         } <- dyn,
         [%{"index" => 0}] <- params["types"],
         true <-
           params["regions"] == [] && params["const_generics"] == [] &&
             params["trait_type_constraints"] == [],
         [
           %{
             "origin" => "Dyn",
             "trait_" => %{"skip_binder" => %{"id" => trait, "generics" => trait_args}}
           }
         ] <- params["trait_clauses"],
         true <- trait_args == %{@args | "types" => [%{"TypeVar" => %{"Bound" => [1, 0]}}]},
         true <- Lynx.Rustler.EncoderModels.encoder_trait?(trait, document["translated"], refs),
         [
           %{
             "regions" => [],
             "outlives" => [],
             "skip_binder" => [%{"Lub" => %{"TypeVar" => %{"Bound" => [1, 0]}}}, region]
           }
         ] <- params["outlives"] do
      region == "Static" ||
        (lifetime == :local && match?(%{"Body" => n} when is_integer(n) and n >= 0, region))
    else
      _ -> false
    end
  end

  defp walk(%{"statements" => statements} = block, state, function) do
    {statements, {state, _}} =
      Enum.map_reduce(statements, {state, []}, fn statement, {state, prefix} ->
        {changed, state} = constructor(statement, prefix, state, function)
        {changed, {state, prefix ++ [statement]}}
      end)

    {%{block | "statements" => statements}, state}
  end

  defp walk(map, state, function) when is_map(map) do
    {pairs, state} =
      Enum.map_reduce(map, state, fn {key, value}, state ->
        {value, state} = walk(value, state, function)
        {{key, value}, state}
      end)

    {Map.new(pairs), state}
  end

  defp walk(list, state, function) when is_list(list),
    do: Enum.map_reduce(list, state, &walk(&1, &2, function))

  defp walk(value, state, _), do: {value, state}

  defp constructor(
         %{
           "kind" => %{
             "Assign" => [place, %{"Aggregate" => [%{"Adt" => [type, variant, nil]}, operands]}]
           }
         } = stmt,
         prefix,
         state,
         function
       ) do
    name = state.variants[variant]

    if type["id"] == state.error["def_id"] && name do
      expected = %{
        "Adt" => %{"id" => state.error["def_id"], "builtin" => nil, "generics" => @args}
      }

      operation =
        if name in ~w(Term RaiseTerm) do
          payload_operation(operands, name, state)
        else
          case operands do
            [operand] ->
              case ErrorLiterals.read(operand, prefix, state) do
                {:ok, text} -> {:ok, %{literal: text, inputs: [], arguments: []}}
                _ -> :error
              end

            _ ->
              :error
          end
        end

      unless type["builtin"] == nil && Constants.empty_arguments?(type["generics"]) &&
               CallModels.expand(place["ty"], state.refs) == expected &&
               match?({:ok, _}, operation),
             do:
               LLBC.failure!(
                 function,
                 state.document["translated"],
                 if(name in ~w(Term RaiseTerm),
                   do:
                     "Rustler #{name} requires a validated boxed Encoder and its compiled Error type",
                   else:
                     "Rustler #{name} requires a validated ASCII literal of at most 255 bytes and its compiled Error type"
                 )
               )

      {:ok, operation} = operation
      {entry, state} = entry(name, operation, state)

      resume = %{
        "span" => stmt["span"],
        "id" => state.next + 1,
        "kind" => "UnwindResume",
        "comments_before" => []
      }

      call = %{
        "call" => %{
          "func" => %{
            "Regular" => %{"kind" => %{"Fun" => entry.declaration["def_id"]}, "generics" => @args}
          },
          "args" => operation.arguments,
          "safety" => "Inherit"
        },
        "dest" => place,
        "on_unwind" => %{"span" => stmt["span"], "id" => state.next, "statements" => [resume]}
      }

      site = %{
        caller: function["def_id"],
        statement: stmt["id"],
        variant: name,
        literal: operation.literal,
        span: stmt["span"]
      }

      {%{stmt | "kind" => %{"Call" => call}},
       %{state | next: state.next + 2, sites: [site | state.sites]}}
    else
      walk(stmt, state, function)
    end
  end

  defp constructor(stmt, _, state, function), do: walk(stmt, state, function)

  defp entry(name, operation, state) do
    text = operation.literal

    case Enum.find(state.entries, &(&1.variant == name && &1.literal == text)) do
      nil ->
        index = length(state.entries)
        {inputs, state} = primitive_inputs(operation.inputs, state)

        path =
          @error ++
            [
              %{
                "Ident" => [
                  "Lynx#{name}#{if text == nil, do: "Payload", else: "Literal"}#{index}",
                  0
                ]
              }
            ]

        type = %{"Adt" => %{"id" => state.error["def_id"], "builtin" => nil, "generics" => @args}}

        decl = %{
          "def_id" => state.first_id + index,
          "src" => "Normal",
          "body" => "Opaque",
          "item_meta" =>
            Map.merge(state.error["item_meta"], %{"name" => path, "opacity" => "Opaque"}),
          "generics" => Map.new(state.error["generics"], fn {k, _} -> {k, []} end),
          "signature" => %{
            "is_unsafe" => false,
            "abi" => "Rust",
            "is_variadic" => false,
            "inputs" => inputs,
            "output" => %{"Value" => [state.reference, type]}
          }
        }

        entry = %{variant: name, literal: text, declaration: decl, index: index}
        {entry, %{state | entries: state.entries ++ [entry], reference: state.reference + 1}}

      entry ->
        {entry, state}
    end
  end

  defp primitive_inputs([], state), do: {[], state}

  # Aeneas represents an owned unsized value with erased lifetime names.
  # Normalize only the foreign primitive's input signature,
  # after validating the actual static Error field and owned Box<dyn Encoder>.
  # Keep original executable operands/types intact and allocate fresh type IDs.
  defp primitive_inputs([type], state) do
    %{"Adt" => box} = unshare(type, state.refs)
    [dynamic] = box["generics"]["types"]
    %{"DynTrait" => predicate} = unshare(dynamic, state.refs)

    predicate =
      update_in(predicate, ["binder", "params", "outlives"], fn [bound] ->
        [update_in(bound, ["skip_binder"], fn [self, _region] -> [self, "Erased"] end)]
      end)

    dynamic = %{"Value" => [state.reference, %{"DynTrait" => predicate}]}
    box = put_in(box, ["generics", "types"], [dynamic])

    {[%{"Value" => [state.reference + 1, %{"Adt" => box}]}],
     %{state | reference: state.reference + 2}}
  end

  defp unshare(%{"Value" => [_, type]}, _), do: type
  defp unshare(%{"Deduplicated" => id}, refs), do: Map.fetch!(refs, id)

  def models!(document, proof, prefix) do
    Map.new(proof.entries, fn entry ->
      decl = entry.declaration

      unless Enum.at(document["translated"]["fun_decls"], decl["def_id"]) == decl,
        do:
          raise(
            ArgumentError,
            "missing or inconsistent validated Rustler atom primitive declaration"
          )

      name =
        "rustler::error::Error::Lynx#{entry.variant}#{if entry.literal == nil, do: "Payload", else: "Literal"}#{entry.index}"

      {decl["def_id"],
       %{
         rust_name: name,
         lean:
           if(entry.literal == nil,
             do:
               "Lynx.Rustler." <>
                 if(entry.variant == "Term",
                   do: "termErrorOutcome",
                   else: "raiseTermErrorOutcome"
                 ),
             else: prefix <> ".ErrorConstants.literal_#{entry.index}"
           ),
         builtin: false,
         can_fail: false,
         lift: false,
         function: decl,
         definition_id: decl["def_id"],
         implementation_verified: false,
         status: :modelled,
         label:
           if(entry.literal == nil,
             do:
               "Rustler #{entry.variant} constructor validated against compiled enum and boxed Encoder; encoding deferred through actual extracted dictionaries; native allocation, reclamation and FFI unverified",
             else:
               "Rustler #{entry.variant}(#{inspect(entry.literal)}) constructor validated against compiled enum and literal; return conversion modelled; atom creation, allocation and native FFI unverified"
           )
       }}
    end)
  end

  def install!(proof, output, prefix, bridge) do
    case Enum.reject(proof.entries, &(&1.literal == nil)) do
      [] -> []
      literals -> install_literals!(literals, output, prefix, bridge)
    end
  end

  defp install_literals!(literals, output, prefix, bridge) do
    name = prefix <> ".ErrorConstants"

    definitions =
      Enum.map_join(literals, "\n", fn entry ->
        operation =
          if entry.variant == "Atom", do: "atomErrorOutcome", else: "raiseAtomErrorOutcome"

        chars = Enum.map_join(:binary.bin_to_list(entry.literal), ", ", &"Char.ofNat #{&1}")

        "@[expose] public abbrev literal_#{entry.index} : Lynx.Rustler.DecoderError := Lynx.Rustler.#{operation} (String.ofList [#{chars}])"
      end)

    path = Path.join(output, String.replace(name, ".", "/") <> ".lean")
    File.mkdir_p!(Path.dirname(path))

    File.write!(
      path,
      "module\npublic import #{bridge}\nnamespace #{name}\n#{definitions}\nend #{name}\n"
    )

    [name]
  end

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
