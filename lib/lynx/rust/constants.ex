defmodule Lynx.Rust.Constants do
  @moduledoc false

  # Immutable scalar/array constants, promoted shared borrows and string literals.
  # Initializer bodies are checked by LLBC alongside ordinary implementations.
  def audit!(globals, initializers, refs, types) do
    declarations = Map.new(globals, &{&1["def_id"], &1})

    if map_size(declarations) != length(globals),
      do: raise(ArgumentError, "duplicate LLBC constant identity")

    for global <- globals do
      unless get_in(global, ["item_meta", "opacity"]) == "Transparent" and
               constant_parameters?(global) do
        raise ArgumentError,
              "missing, opaque or generic Rust constant: #{inspect(global["def_id"])}"
      end

      type = unwrap(global["ty"], refs)

      case {global["global_kind"], constant_value(global["value"])} do
        {kind, [%{"Call" => [%{"kind" => %{"Fun" => id}, "generics" => args}, []]}, value_type]}
        when kind in ["NamedConst", "AnonConst"] ->
          initializer = Enum.find(initializers, &(&1["def_id"] == id))

          unless supported_initializer_type?(global, type, refs) and
                   unwrap(value_type, refs) == type and identity_arguments?(global, args) and
                   initializer != nil and
                   get_in(initializer, ["src", "GlobalInitializer", "id"]) == global["def_id"] and
                   identity_arguments?(
                     global,
                     get_in(initializer, ["src", "GlobalInitializer", "generics"])
                   ) and
                   initializer["generics"] == global["generics"] and
                   get_in(initializer, ["item_meta", "name"]) ==
                     get_in(global, ["item_meta", "name"]) and
                   get_in(initializer, ["signature", "inputs"]) == [] and
                   unwrap(get_in(initializer, ["signature", "output"]), refs) == type do
            raise ArgumentError,
                  "missing or inconsistent Rust constant initializer: #{global["def_id"]}"
          end

        {"AnonConst", [%{"Str" => value}, value_type]} when is_binary(value) ->
          unless String.valid?(value) and unwrap(value_type, refs) == type and
                   str_type?(type, types, refs),
                 do: raise(ArgumentError, "Rust string constant has an inconsistent type")

        _ ->
          raise ArgumentError,
                "unsupported Rust global: only scalar/array const initializers, promoted shared scalar/array borrows and string literals are supported (#{inspect(global["global_kind"])})"
      end
    end

    for initializer <- initializers do
      id = get_in(initializer, ["src", "GlobalInitializer", "id"])

      unless Map.has_key?(declarations, id) and
               initializer_id(declarations[id]) == initializer["def_id"],
             do: raise(ArgumentError, "orphaned Rust constant initializer: #{inspect(id)}")
    end

    declarations
  end

  def link!(declarations, translation) do
    for {id, global} <- declarations,
        initializer_id(global) != nil or not is_nil(global["lynx_scalar_model"]) or
          not is_nil(global["lynx_vtable"]),
        into: %{} do
      matches = Enum.filter(Map.get(translation, "globals", []), &(&1["def_id"] == id))

      case {global["lynx_scalar_model"], global["global_kind"], matches} do
        {nil, "VTable", []} ->
          {id, Lynx.Rust.VTables.link!(global, translation)}

        {%{} = model, "NamedConst", []} ->
          {id,
           model
           |> Map.put("def_id", id)
           |> Map.put("modelled", true)
           |> Map.put("declaration", global)}

        {nil, "AnonConst", []} ->
          # Pinned Aeneas replaces promoted reads with calls and inlines the
          # checked initializer (anon_consts_to_calls / inline_anon_const_initializers).
          # There is deliberately no invented Lean declaration for that initializer.
          name =
            Enum.map_join(global["item_meta"]["name"], "::", fn
              %{"Ident" => [name, _]} -> name
              %{"Builtin" => ["PromotedConst", index]} -> "{promoted const##{index}}"
              other -> JSON.encode!(other)
            end)

          {id,
           %{
             "def_id" => id,
             "rust_name" => name,
             "inlined" => true,
             "initializer_id" => initializer_id(global),
             "declaration" => global
           }}

        {nil, _, [%{"lean_name" => name, "lean_file" => file, "can_fail" => can_fail} = model]}
        when is_binary(name) and is_binary(file) and is_boolean(can_fail) ->
          {id, Map.put(model, "declaration", global)}

        _ ->
          raise ArgumentError, "missing or inconsistent Aeneas constant definition: #{id}"
      end
    end
  end

  def initializer_id(%{"lynx_scalar_model" => _}), do: nil

  def initializer_id(global) do
    case constant_value(global["value"]) do
      [%{"Call" => [%{"kind" => %{"Fun" => id}}, []]}, _] -> id
      _ -> nil
    end
  end

  defp supported_initializer_type?(%{"global_kind" => "NamedConst"}, type, refs),
    do: scalar_or_array?(type, refs)

  defp supported_initializer_type?(
         %{"global_kind" => "AnonConst", "item_meta" => %{"name" => name}},
         %{"Ref" => ["Erased", element, "Shared"]},
         refs
       ) do
    match?(
      %{"Builtin" => ["PromotedConst", index]} when is_integer(index) and index >= 0,
      List.last(name)
    ) and scalar_or_array?(unwrap(element, refs), refs)
  end

  defp supported_initializer_type?(_, _, _), do: false

  defp scalar_or_array?(%{"Array" => [element, length, nil]}, refs) do
    usize = %{"Scalar" => %{"Integer" => %{"Unsigned" => "Usize"}}}

    # Lengths use the constant family, even when their IDs overlap type IDs.
    literal =
      case length do
        %{"Value" => [_, value]} -> value
        value -> value
      end

    case literal do
      [%{"Integer" => %{"Unsigned" => ["Usize", value]}}, type] when is_binary(value) ->
        scalar?(unwrap(element, refs)) and unwrap(type, refs) == usize and
          case Integer.parse(value) do
            {count, ""} -> count >= 0 and Integer.to_string(count) == value
            _ -> false
          end

      _ ->
        false
    end
  end

  defp scalar_or_array?(type, _refs), do: scalar?(type)

  defp str_type?(%{"Adt" => %{"id" => id, "builtin" => "Str", "generics" => args}}, types, refs) do
    empty_arguments?(args) and
      Enum.any?(types, fn
        %{
          "def_id" => ^id,
          "item_meta" => %{"name" => [%{"Builtin" => ["Str", 0]}]},
          "generics" => generics,
          "kind" => %{"Struct" => [%{"ty" => field_type}]}
        } ->
          empty_parameters?(generics) and
            case unwrap(field_type, refs) do
              %{"Slice" => [element, nil]} ->
                unwrap(element, refs) == %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}

              _ ->
                false
            end

        _ ->
          false
      end)
  end

  defp str_type?(_, _, _), do: false

  defp constant_value(%{"Value" => [_, value]}), do: value
  defp constant_value(_), do: :unsupported_constant_value

  # Rust promotions may inherit lifetime parameters from their enclosing
  # function. Only shared erased scalar/array promotions qualify; their real bodies
  # remain audited and Aeneas handles the lifetime parameters normally.
  defp constant_parameters?(global) do
    params = global["generics"]

    empty_parameters?(params) or
      (global["global_kind"] == "AnonConst" and initializer_id(global) != nil and
         is_map(params) and lifetime_parameters?(params))
  end

  defp lifetime_parameters?(params) do
    regions = params["regions"]

    is_list(regions) and regions != [] and
      Enum.all?(Enum.with_index(regions), fn {region, index} -> region["index"] == index end) and
      Enum.all?(
        ~w(types const_generics trait_clauses trait_type_constraints),
        &(params[&1] == [])
      ) and
      Map.get(params, "outlives", []) == []
  end

  defp identity_arguments?(global, args) do
    params = global["generics"]

    expected = %{
      "regions" =>
        Enum.map(params["regions"], fn region ->
          %{"Var" => %{"Free" => region["index"]}}
        end),
      "types" => [],
      "const_generics" => [],
      "trait_refs" => []
    }

    args == expected
  end

  def arguments?(
        %{"generics" => params} = global,
        %{"regions" => regions, "types" => [], "const_generics" => [], "trait_refs" => []},
        caller
      )
      when is_list(regions) do
    constant_parameters?(global) and length(regions) == length(params["regions"]) and
      Enum.all?(regions, fn
        %{"Var" => %{"Free" => index}} when is_integer(index) and index >= 0 ->
          Enum.any?(caller["generics"]["regions"], &(&1["index"] == index))

        %{"Body" => index} when is_integer(index) and index >= 0 ->
          # The actual function body binds these regions separately from its
          # signature. Keep the compiler binder and reject out-of-scope IDs.
          count = get_in(caller, ["body", "Structured", "bound_body_regions"])
          is_integer(count) and index < count

        _ ->
          false
      end)
  end

  def arguments?(_, _, _), do: false

  def empty_arguments?(%{
        "regions" => [],
        "types" => [],
        "const_generics" => [],
        "trait_refs" => []
      }),
      do: true

  def empty_arguments?(_), do: false

  defp empty_parameters?(
         %{
           "regions" => [],
           "types" => [],
           "const_generics" => [],
           "trait_clauses" => [],
           "trait_type_constraints" => []
         } = params
       ),
       do: Map.get(params, "outlives", []) == []

  defp empty_parameters?(_), do: false

  defp scalar?(%{"Scalar" => "Bool"}), do: true

  defp scalar?(%{"Scalar" => %{"Integer" => %{"Unsigned" => width}}}),
    do: width in ~w(U8 U16 U32 U64 U128 Usize)

  defp scalar?(%{"Scalar" => %{"Integer" => %{"Signed" => width}}}),
    do: width in ~w(I8 I16 I32 I64 I128 Isize)

  defp scalar?(_), do: false

  # Values and types have separate Charon hash-cons tables. Const values are
  # unwrapped only at their explicit Value wrapper; only types use this table.
  defp unwrap(%{"Value" => [id, value]}, refs), do: Map.get(refs, id, value)
  defp unwrap(%{"Deduplicated" => id}, refs), do: Map.get(refs, id)
  defp unwrap(value, _refs), do: value
end
