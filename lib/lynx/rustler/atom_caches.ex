defmodule Lynx.Rustler.AtomCaches do
  @moduledoc false

  alias Lynx.Rust.CallModels

  # Structural expansion metadata does not resolve names: even std and rustler
  # may be shadowed by application modules. Check the compiler's nominal types
  # and calls before considering a generated cache as an FFI model candidate.
  # This result does not admit opaque first-party code or verify a cache.
  def resolve!(document, caches) do
    translated = document["translated"]
    refs = Lynx.Rust.LLBC.type_references!(document)
    types = Map.new(Enum.reject(translated["type_decls"], &is_nil/1), &{&1["def_id"], &1})
    functions = Enum.reject(translated["fun_decls"], &is_nil/1)
    crate = translated["crate_name"]

    Enum.map(caches, fn cache ->
      prefix = identifiers([crate | cache["modules"]])

      type =
        unique!(
          Map.values(types),
          &(&1["item_meta"]["name"] == prefix ++ identifiers([cache["structure"]]))
        )

      type_id = type["def_id"]

      fields =
        case type["kind"] do
          %{"Struct" => fields} -> fields
          _ -> fail!("cache is not a struct")
        end

      unless Enum.map(fields, & &1["name"]) == Enum.map(cache["fields"], & &1["field"]) and
               Enum.all?(fields, &(nominal(&1["ty"], types, refs) == ~w(rustler types atom Atom))),
             do: fail!("cache fields do not have the resolved Rustler Atom type")

      factory =
        unique!(functions, fn function ->
          case function["item_meta"]["name"] do
            name when length(name) == length(prefix) + 2 ->
              {head, tail} = Enum.split(name, length(prefix))

              head == prefix and
                match?([%{"Impl" => %{"Ty" => _}}, %{"Ident" => ["get", 0]}], tail) and
                impl_type(hd(tail), refs) == type_id

            _ ->
              false
          end
        end)

      signature = factory["signature"]

      unless match?(
               %{"is_unsafe" => false, "abi" => "Rust", "is_variadic" => false, "inputs" => []},
               signature
             ) and
               match?(
                 %{"Ref" => ["Static", %{"Adt" => %{"id" => ^type_id}}, "Shared"]},
                 CallModels.expand(signature["output"], refs)
               ),
             do: fail!("cache factory signature is not fn() -> &'static RustlerAtoms")

      name = factory["item_meta"]["name"]

      global =
        unique!(Enum.reject(translated["global_decls"], &is_nil/1), fn global ->
          global["item_meta"]["name"] == name ++ identifiers(["RUSTLER_ATOMS"])
        end)

      unless global["global_kind"] ==
               %{"Static" => %{"is_mut" => false, "is_safe" => true, "is_thread_local" => false}} and
               nominal(global["ty"], types, refs) == ~w(std sync once_lock OnceLock) and
               match?(
                 %{"Adt" => %{"generics" => %{"types" => [%{"Adt" => %{"id" => ^type_id}}]}}},
                 CallModels.expand(global["ty"], refs)
               ),
             do: fail!("cache global is not a read-only OnceLock<RustlerAtoms>")

      family = Enum.filter(functions, &(Enum.take(&1["item_meta"]["name"], length(name)) == name))
      ids = MapSet.new(Enum.map(family, & &1["def_id"]))
      by_id = Map.new(functions, &{&1["def_id"], &1})

      calls =
        family
        |> Enum.flat_map(&calls(&1["body"]))
        |> Enum.uniq()
        |> Enum.reject(&MapSet.member?(ids, &1))
        |> Enum.map(fn id ->
          function = Map.fetch!(by_id, id)
          resolved_call(function["item_meta"]["name"], types, refs)
        end)
        |> MapSet.new()

      expected =
        MapSet.new([
          {~w(std sync once_lock OnceLock), "get_or_init"},
          {~w(std sync once_lock OnceLock), "new"},
          {~w(rustler env OwnedEnv), "new"},
          {~w(rustler env OwnedEnv), "run"},
          {~w(rustler env OwnedEnv), "drop"},
          {~w(rustler types atom Atom), "from_str"},
          {~w(core result Result), "expect"}
        ])

      unless calls == expected, do: fail!("cache uses unresolved or unsupported runtime calls")

      %{
        type_id: type_id,
        factory_id: factory["def_id"],
        global_id: global["def_id"],
        factory_name: name,
        fields: cache["fields"],
        implementation_verified: false
      }
    end)
  end

  defp identifiers(names), do: Enum.map(names, &%{"Ident" => [&1, 0]})

  defp nominal(type, types, refs) do
    case CallModels.expand(type, refs) do
      %{"Adt" => %{"id" => id}} ->
        case types[id] do
          %{"item_meta" => %{"name" => name}} ->
            Enum.map(name, fn
              %{"Ident" => [part, 0]} -> part
              _ -> nil
            end)

          _ ->
            nil
        end

      _ ->
        nil
    end
  end

  defp impl_type(%{"Impl" => %{"Ty" => %{"skip_binder" => type}}}, refs) do
    case CallModels.expand(type, refs) do
      %{"Adt" => %{"id" => id}} -> id
      _ -> nil
    end
  end

  defp resolved_call(name, types, refs) do
    case Enum.reverse(name) do
      [%{"Ident" => [method, 0]}, %{"Impl" => %{"Ty" => %{"skip_binder" => type}}} | _] ->
        {nominal(type, types, refs), method}

      [%{"Builtin" => ["DropGlue", 0]}, %{"Impl" => %{"Trait" => _}} | reversed] ->
        {Enum.map(Enum.reverse(reversed), fn %{"Ident" => [part, 0]} -> part end), "drop"}

      _ ->
        nil
    end
  end

  defp calls(%{"Fun" => id}) when is_integer(id), do: [id]
  defp calls(map) when is_map(map), do: Enum.flat_map(Map.values(map), &calls/1)
  defp calls(list) when is_list(list), do: Enum.flat_map(list, &calls/1)
  defp calls(_), do: []

  defp unique!(items, predicate) do
    case Enum.filter(items, predicate) do
      [item] -> item
      _ -> fail!("missing or ambiguous compiled cache identity")
    end
  end

  defp fail!(message),
    do: raise(ArgumentError, "unsupported compiled Rustler atom cache: #{message}")
end
