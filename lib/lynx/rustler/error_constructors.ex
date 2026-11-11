defmodule Lynx.Rustler.ErrorConstructors do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Constants, LLBC}
  @name Enum.map(~w(rustler error Error), &%{"Ident" => [&1, 0]})
  @constructor @name ++ [%{"Ident" => ["BadArg", 0]}]
  @arguments %{"regions" => [], "types" => [], "const_generics" => [], "trait_refs" => []}

  def needed?(document, first_party) do
    case error_type(document) do
      nil ->
        false

      error ->
        Enum.any?(functions(document, first_party), &constructs?(&1["body"], error["def_id"])) ||
          Lynx.Rustler.ErrorDrops.needed?(document, first_party)
    end
  end

  # Model validated foreign constructor operations, not Rust function bodies.
  # Keep Error opaque: no dummy fields or erasure of its unsupported variants.
  def lower!(document, layout, first_party, prefix \\ "Rust") do
    {document, badarg} = lower_badarg!(document, layout, first_party)
    {document, values} = Lynx.Rustler.ValueConstructors.lower!(document, layout, first_party)
    reject_remaining!(document, layout, first_party)
    {document, drops} = Lynx.Rustler.ErrorDrops.lower!(document, layout, first_party)

    constructors =
      if(values, do: %{badarg: badarg, values: Map.put(values, :prefix, prefix)}, else: badarg)

    {document, if(drops, do: %{constructors: constructors, drops: drops}, else: constructors)}
  end

  defp reject_remaining!(document, layout, first_party) do
    error = error_type(document)
    variants = error_type(layout)["kind"]["Enum"]

    for function <- functions(document, first_party) do
      reject_constructor!(
        function["body"],
        error["def_id"],
        variants,
        function,
        document["translated"]
      )
    end
  end

  defp reject_constructor!(
         %{"Aggregate" => [%{"Adt" => [%{"id" => id}, variant, _]}, _]},
         id,
         variants,
         function,
         translated
       ) do
    case Enum.find(variants, &(&1["id"] == variant)) do
      %{"name" => name} ->
        detail =
          if name in ["Term", "RaiseTerm"],
            do:
              "dynamic Encoder payloads require verified dispatch, deferred encoding, panic and destruction semantics",
            else: "the constructor is outside the validated Rustler Error subset"

        LLBC.failure!(
          function,
          translated,
          "unsupported Rustler Error::#{name} construction: #{detail}"
        )

      _ ->
        LLBC.failure!(
          function,
          translated,
          "inconsistent compiled Rustler Error constructor identity"
        )
    end
  end

  defp reject_constructor!(map, id, variants, function, translated) when is_map(map),
    do: Enum.each(Map.values(map), &reject_constructor!(&1, id, variants, function, translated))

  defp reject_constructor!(list, id, variants, function, translated) when is_list(list),
    do: Enum.each(list, &reject_constructor!(&1, id, variants, function, translated))

  defp reject_constructor!(_, _, _, _, _), do: :ok

  defp lower_badarg!(document, layout, first_party) do
    if "rustler" in first_party,
      do:
        raise(
          ArgumentError,
          "Rustler constructor models cannot assume first-party Error semantics"
        )

    error = error_type(document)
    full = error_type(layout)

    unless error && error["kind"] == "Opaque" && full &&
             error["item_meta"]["has_errors"] == false && full["item_meta"]["has_errors"] == false &&
             Enum.all?(Map.values(error["generics"]), &(&1 == [])) &&
             Enum.all?(Map.values(full["generics"]), &(&1 == [])),
           do:
             raise(
               ArgumentError,
               "BadArg construction requires the actual opaque Rustler Error model and compiled enum layout"
             )

    variant =
      case full["kind"] do
        %{"Enum" => variants} ->
          case Enum.filter(variants, &(&1["name"] == "BadArg")) do
            [%{"id" => id, "fields" => []} = variant] when is_integer(id) and id >= 0 ->
              if Enum.at(variants, id) != variant,
                do: raise(ArgumentError, "inconsistent compiled Rustler BadArg variant identity")

              variant

            _ ->
              raise ArgumentError, "missing or nonempty compiled Rustler BadArg constructor"
          end

        _ ->
          raise ArgumentError, "Rustler Error constructor requires its compiled enum layout"
      end

    translated = document["translated"]
    funs = translated["fun_decls"]

    for {function, index} <- Enum.with_index(funs), function != nil do
      unless function["def_id"] == index,
        do: raise(ArgumentError, "inconsistent LLBC function table")

      if function["item_meta"]["name"] == @constructor,
        do: raise(ArgumentError, "Rustler BadArg constructor primitive identity collision")
    end

    refs = LLBC.type_references!(document)

    initial = %{
      next: max_id(document) + 1,
      sites: [],
      function_id: length(funs),
      error_id: error["def_id"],
      variant_id: variant["id"],
      refs: refs
    }

    {funs, state} =
      Enum.map_reduce(funs, initial, fn function, state ->
        if function && first_party?(function, first_party) do
          {body, state} = walk(function["body"], state, function, translated)
          {%{function | "body" => body}, state}
        else
          {function, state}
        end
      end)

    if state.sites == [] do
      {document, nil}
    else
      type = %{"Adt" => %{"id" => error["def_id"], "builtin" => nil, "generics" => @arguments}}
      reference = Enum.max(Map.keys(refs), fn -> -1 end) + 1

      declaration = %{
        "def_id" => state.function_id,
        "src" => "Normal",
        "body" => "Opaque",
        "item_meta" =>
          Map.merge(error["item_meta"], %{
            "name" => @constructor,
            "opacity" => "Opaque"
          }),
        "generics" => Map.new(full["generics"], fn {key, _} -> {key, []} end),
        "signature" => %{
          "is_unsafe" => false,
          "abi" => "Rust",
          "is_variadic" => false,
          "inputs" => [],
          "output" => %{"Value" => [reference, type]}
        }
      }

      positions =
        Enum.with_index(translated["ordered_decls"])
        |> Enum.filter(fn {entry, _} -> entry == %{"Type" => %{"NonRec" => error["def_id"]}} end)

      position =
        case positions do
          [{_, position}] ->
            position

          _ ->
            raise ArgumentError,
                  "missing or inconsistent compiled Rustler Error declaration order"
        end

      document =
        document
        |> put_in(["translated", "fun_decls"], funs ++ [declaration])
        |> update_in(
          ["translated", "item_names"],
          &(&1 ++ [%{"key" => %{"Fun" => state.function_id}, "value" => @constructor}])
        )
        |> update_in(
          ["translated", "ordered_decls"],
          &List.insert_at(&1, position + 1, %{"Fun" => %{"NonRec" => state.function_id}})
        )

      {document,
       %{
         declaration: declaration,
         sites: Enum.reverse(state.sites),
         layout: full,
         variant: variant,
         function_id: state.function_id
       }}
    end
  end

  def boundary(%{constructors: constructors, drops: _}),
    do:
      boundary(constructors) ++
        [
          "Partial Rustler Result destruction model: boxed errors and unsupported Ok payloads exhaust verification; scalar Ok destruction requires compiler-validated primitive types; compiler glue and native SDK remain trusted"
        ]

  def boundary(nil), do: []

  def boundary(%{values: _} = proof),
    do:
      boundary(proof.badarg) ++
        [
          "Lynx validated lowering of foreign Rustler value error constructors; allocation, reclamation and native FFI remain unverified"
        ] ++
        if(Enum.any?(proof.values.entries, &(&1.literal == nil)),
          do: [
            "Foreign owned Box<dyn Encoder> constructor-signature lifetime names normalized for Aeneas; original executable operands and types retained"
          ],
          else: []
        )

  def boundary(_proof),
    do: ["Lynx validated lowering of foreign Rustler BadArg constructor operations"]

  def models!(document, %{constructors: constructors, drops: drops}),
    do:
      Map.merge(models!(document, constructors), Lynx.Rustler.ErrorDrops.models!(document, drops))

  def models!(_document, nil), do: %{}

  def models!(document, %{values: values, badarg: badarg}),
    do:
      Map.merge(
        models!(document, badarg),
        Lynx.Rustler.ValueConstructors.models!(document, values, values.prefix)
      )

  def models!(document, proof) do
    unless Enum.at(document["translated"]["fun_decls"], proof.function_id) == proof.declaration,
      do:
        raise(
          ArgumentError,
          "missing or inconsistent validated Rustler BadArg primitive declaration"
        )

    %{
      proof.function_id => %{
        rust_name: "rustler::error::Error::BadArg",
        lean: "Lynx.Rustler.badArgOutcome",
        builtin: false,
        can_fail: false,
        lift: false,
        function: proof.declaration,
        definition_id: proof.function_id,
        implementation_verified: false,
        status: :modelled,
        label:
          "Rustler BadArg constructor primitive validated against compiled enum identity; return conversion modelled, Rustler and native FFI unverified"
      }
    }
  end

  def install!(%{constructors: constructors}, output, prefix, models),
    do: install!(constructors, output, prefix, models)

  def install!(%{values: values}, output, prefix, models) do
    bridge = Enum.find(models, &(&1.rust == "rustler::error::Error"))
    Lynx.Rustler.ValueConstructors.install!(values, output, prefix, bridge.import)
  end

  def install!(_, _, _, _), do: []

  defp walk(
         %{
           "kind" => %{
             "Assign" => [place, %{"Aggregate" => [%{"Adt" => [type, variant, nil]}, []]}]
           }
         } = statement,
         state,
         function,
         translated
       )
       when variant == state.variant_id do
    if type["id"] == state.error_id do
      expected = %{"Adt" => %{"id" => state.error_id, "builtin" => nil, "generics" => @arguments}}

      unless type["builtin"] == nil && Constants.empty_arguments?(type["generics"]) &&
               CallModels.expand(place["ty"], state.refs) == expected,
             do:
               LLBC.failure!(
                 function,
                 translated,
                 "inconsistent Rustler BadArg constructor type or arguments"
               )

      resume = %{
        "span" => statement["span"],
        "id" => state.next + 1,
        "kind" => "UnwindResume",
        "comments_before" => []
      }

      # Constructor evaluation cannot unwind. The schema requires a cleanup
      # block for every call; the admitted primitive is infallible and allocates
      # nothing, so this synthetic resume branch is unreachable.
      call = %{
        "call" => %{
          "func" => %{
            "Regular" => %{"kind" => %{"Fun" => state.function_id}, "generics" => @arguments}
          },
          "args" => [],
          "safety" => "Inherit"
        },
        "dest" => place,
        "on_unwind" => %{
          "span" => statement["span"],
          "id" => state.next,
          "statements" => [resume]
        }
      }

      site = %{caller: function["def_id"], statement: statement["id"], span: statement["span"]}

      {%{statement | "kind" => %{"Call" => call}},
       %{state | next: state.next + 2, sites: [site | state.sites]}}
    else
      walk_children(statement, state, function, translated)
    end
  end

  defp walk(value, state, function, translated),
    do: walk_children(value, state, function, translated)

  defp walk_children(map, state, function, translated) when is_map(map) do
    {pairs, state} =
      Enum.map_reduce(map, state, fn {k, v}, state ->
        {v, state} = walk(v, state, function, translated)
        {{k, v}, state}
      end)

    {Map.new(pairs), state}
  end

  defp walk_children(list, state, function, translated) when is_list(list),
    do: Enum.map_reduce(list, state, &walk(&1, &2, function, translated))

  defp walk_children(value, state, _, _), do: {value, state}

  defp constructs?(%{"Aggregate" => [%{"Adt" => [%{"id" => id}, _, _]}, _]}, id), do: true
  defp constructs?(map, id) when is_map(map), do: Enum.any?(Map.values(map), &constructs?(&1, id))
  defp constructs?(list, id) when is_list(list), do: Enum.any?(list, &constructs?(&1, id))
  defp constructs?(_, _), do: false

  defp error_type(document) do
    case Enum.filter(
           document["translated"]["type_decls"],
           &(&1 && &1["item_meta"]["name"] == @name)
         ) do
      [] -> nil
      [type] -> type
      _ -> raise ArgumentError, "ambiguous compiled Rustler Error identity"
    end
  end

  defp functions(document, first_party),
    do: Enum.filter(document["translated"]["fun_decls"], &(&1 && first_party?(&1, first_party)))

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
