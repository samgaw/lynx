defmodule Lynx.Rustler.DecoderValues do
  @moduledoc false
  alias Lynx.Rust.{CallModels, Constants, DropModels, LLBC, ResourceModels}

  # Decoded arguments can outlive later decoding failures; return values live
  # until encoding completes. Require compiler no-drop evidence and inspect
  # every field: even a no-drop Rust type can own
  # modeled mutex/atomic/resource cells, which need explicit lifetime handling.
  def validate!(id, audit, codec \\ :decoder) do
    name = if codec == :encoder, do: "Encoder", else: "Decoder"
    type = %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => ResourceModels.args([])}}

    unless value?(type, audit, [], 32) do
      declaration = Enum.find(audit.translated["type_decls"], &(&1 && &1["def_id"] == id))

      unless declaration,
        do: raise(ArgumentError, "missing runtime Rustler #{name} payload type #{id}")

      LLBC.failure!(
        declaration,
        Map.put_new(audit.translated, "files", []),
        "runtime Rustler #{name} payload requires compiler-validated destructor-free scalar structs/enums or tuples; native owners, opaque fields and unsupported layouts require explicit cleanup"
      )
    end
  end

  defp value?(_, _, _, 0), do: false

  defp value?(type, audit, seen, depth) do
    case CallModels.expand(type, audit.references) do
      %{"Adt" => %{"builtin" => "Tuple", "generics" => args}} ->
        Constants.empty_arguments?(%{args | "types" => []}) and
          Enum.all?(args["types"], &value?(&1, audit, seen, depth - 1))

      %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} ->
        with true <- id not in seen and Constants.empty_arguments?(args),
             %{"needs_drop" => false, "generics" => params, "item_meta" => meta, "kind" => kind} <-
               Enum.find(audit.translated["type_decls"], &(&1 && &1["def_id"] == id)),
             true <- Enum.all?(Map.values(params), &(&1 == [])),
             [%{"Ident" => [crate, 0]} | _] <- meta["name"],
             true <- crate in audit.first_party,
             true <- meta["has_errors"] == false,
             fields when is_list(fields) <- fields(kind) do
          Enum.all?(fields, &value?(&1["ty"], audit, [id | seen], depth - 1))
        else
          _ -> false
        end

      scalar ->
        DropModels.primitive_scalar?(scalar)
    end
  end

  defp fields(%{"Struct" => fields}), do: fields
  defp fields(%{"Enum" => variants}), do: Enum.flat_map(variants, & &1["fields"])
  defp fields(_), do: nil
end
