defmodule Lynx.Rust.NativeGuardStorage do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LockModels}
  @rust "std::sync::poison::mutex::MutexGuard"

  # NativeGuard is the already-admitted runtime capability model, with no Rust
  # lifetime parameter. Apply that representation consistently to saved guards
  # after the original bodies, guard borrows and linear ownership are audited.
  # Explicit &/&mut borrows and every executable statement are retained.
  def lower!(document, audit, models, :cancelling) do
    types = document["translated"]["type_decls"]
    guard = Enum.find(types, &LockModels.guard?(&1, audit.references))

    if guard && saved?(types, guard["def_id"], audit.references) do
      unless Enum.any?(models, &(&1.rust == @rust and &1.lean == "Lynx.NativeGuard")),
        do:
          raise(ArgumentError, "saved guard requires the validated NativeGuard capability model")

      id = guard["def_id"]
      document = rewrite(document, id)

      document =
        update_in(document, ["translated", "type_decls"], fn types ->
          Enum.map(types, fn type ->
            if type && type["def_id"] == id,
              do:
                update_in(
                  type,
                  ["generics"],
                  &Map.merge(&1, %{"regions" => [], "outlives" => []})
                ),
              else: type
          end)
        end)

      {document, [%{type_id: id, rust: @rust, representation: :native_guard_capability}]}
    else
      {document, []}
    end
  end

  def lower!(document, _, _, _), do: {document, []}

  def pattern(pattern, []), do: pattern
  def pattern(pattern, [_]), do: String.replace(pattern, "MutexGuard<'0, ", "MutexGuard<")

  defp saved?(types, guard, refs) do
    Enum.any?(types, fn
      %{
        "kind" => %{"Struct" => fields},
        "item_meta" => %{"attr_info" => %{"attributes" => attributes}}
      } ->
        Enum.any?(
          attributes,
          &match?(%{"Unknown" => %{"path" => "lynx::coroutine_storage_v1"}}, &1)
        ) &&
          Enum.any?(fields, fn field ->
            String.starts_with?(field["name"] || "", "saved_") &&
              contains?(CallModels.expand(field["ty"], refs), guard)
          end)

      _ ->
        false
    end)
  end

  defp contains?(%{"Adt" => %{"id" => id, "builtin" => nil}}, id), do: true
  defp contains?(map, id) when is_map(map), do: Enum.any?(Map.values(map), &contains?(&1, id))
  defp contains?(list, id) when is_list(list), do: Enum.any?(list, &contains?(&1, id))
  defp contains?(_, _), do: false

  defp rewrite(%{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} = type, id) do
    unless length(args["regions"]) == 1,
      do: raise(ArgumentError, "inconsistent saved native guard lifetime arity")

    put_in(type, ["Adt", "generics"], args |> Map.put("regions", []) |> rewrite(id))
  end

  defp rewrite(map, id) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, rewrite(value, id)} end)

  defp rewrite(list, id) when is_list(list), do: Enum.map(list, &rewrite(&1, id))
  defp rewrite(value, _), do: value
end
