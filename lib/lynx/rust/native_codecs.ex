defmodule Lynx.Rust.NativeCodecs do
  @moduledoc false
  alias Lynx.Rust.CallModels

  # Only actual monomorphic first-party structs with named fields are derived.
  # NativeCodec is an internal lossless heap representation, never a Rustler codec.
  def plan!(audit) do
    constructors =
      for {id, model} <- audit.external_calls,
          model[:native_constructor] == true or model[:native_codec_input] == true or
            model[:native_codec_drop] == true or model[:resource_operation] != nil,
          into: %{},
          do:
            {id,
             cond do
               model[:resource_operation] -> :resource
               model[:native_codec_drop] -> :drop
               true -> model[:native_codec_input] == true
             end}

    roots = Enum.flat_map(audit.functions, &payloads(&1["body"], constructors, audit.references))
    plan = Enum.reduce(roots, [], &visit!(&1, audit, &2, []))

    Enum.map(plan, fn type ->
      schema = schema!(type, audit, Map.new(plan, &{&1["def_id"], &1}))

      cleanup =
        if get_in(audit.translated, ["options", "owned_drops"]) == true do
          if type["needs_drop"] == false do
            :trivial
          else
            payload = %{
              "Adt" => %{
                "id" => type["def_id"],
                "builtin" => nil,
                "generics" => Lynx.Rust.ResourceModels.args([])
              }
            }

            case Lynx.Rust.NativeOwnedDrops.function_for(
                   payload,
                   audit.translated,
                   audit.references
                 ) do
              nil -> nil
              function -> function["def_id"]
            end
          end
        end

      type |> Map.put(:native_tag, JSON.encode!(schema)) |> Map.put(:native_cleanup, cleanup)
    end)
  end

  defp payloads(%{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => generics}}, ids, refs) do
    case {Map.fetch(ids, id), generics} do
      {{:ok, :resource},
       %{"types" => [type], "regions" => regions, "const_generics" => [], "trait_refs" => [_]}}
      when length(regions) <= 1 ->
        [type]

      {{:ok, :drop},
       %{"types" => [type], "regions" => [], "const_generics" => [], "trait_refs" => [_]}} ->
        case CallModels.expand(type, refs) do
          %{"Adt" => %{"generics" => %{"types" => [payload]}}} -> [payload]
          %{"Adt" => %{"generics" => %{"types" => []}}} -> [type]
          _ -> raise ArgumentError, "unsupported native consuming codec input"
        end

      {{:ok, false},
       %{"types" => [type], "regions" => [], "const_generics" => [], "trait_refs" => []}} ->
        [type]

      {{:ok, true},
       %{
         "types" => [type],
         "regions" => [%{"Body" => region}],
         "const_generics" => [],
         "trait_refs" => []
       }}
      when is_integer(region) ->
        [type]

      {:error, _} ->
        []

      _ ->
        raise ArgumentError, "unsupported native mutex constructor or acquisition arguments"
    end
  end

  defp payloads(map, ids, refs) when is_map(map),
    do: Enum.flat_map(Map.values(map), &payloads(&1, ids, refs))

  defp payloads(list, ids, refs) when is_list(list),
    do: Enum.flat_map(list, &payloads(&1, ids, refs))

  defp payloads(_, _, _), do: []

  defp visit!(type, audit, found, visiting) do
    case CallModels.expand(type, audit.references) do
      %{"Scalar" => "Bool"} ->
        found

      %{"Scalar" => %{"Integer" => %{"Unsigned" => width}}}
      when width in ~w(U8 U16 U32 U64 U128 Usize) ->
        found

      %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => %{"types" => [payload]} = args}} ->
        type = Enum.find(audit.translated["type_decls"], &(&1 && &1["def_id"] == id))

        unless Lynx.Rust.MutexModels.type?(type) and
                 args == Lynx.Rust.ResourceModels.args([payload]),
               do: raise(ArgumentError, "unsupported native heap handle identity")

        visit!(payload, audit, found, visiting)

      %{
        "Adt" => %{
          "id" => id,
          "builtin" => nil,
          "generics" => %{
            "types" => [],
            "regions" => [],
            "const_generics" => [],
            "trait_refs" => []
          }
        }
      } ->
        cond do
          file_capability?(id, audit) or error_capability?(id, audit) ->
            found

          Enum.any?(found, &(&1["def_id"] == id)) ->
            found

          id in visiting ->
            raise ArgumentError, "recursive native heap payloads are unsupported"

          true ->
            declaration = Enum.find(audit.translated["type_decls"], &(&1 && &1["def_id"] == id))

            unless supported?(declaration, audit.first_party),
              do: raise(ArgumentError, "unsupported native heap struct identity #{id}")

            found =
              Enum.reduce(
                declaration["kind"]["Struct"],
                found,
                &visit!(&1["ty"], audit, &2, [id | visiting])
              )

            found ++ [declaration]
        end

      other ->
        raise ArgumentError, "unsupported native heap payload: #{inspect(other)}"
    end
  end

  defp supported?(
         %{
           "generics" => params,
           "kind" => %{"Struct" => fields},
           "item_meta" => %{"name" => [%{"Ident" => [crate, 0]} | _], "attr_info" => attrs}
         },
         first_party
       ) do
    crate in first_party and empty_parameters?(params) and
      attrs["rename"] == nil and
      Enum.all?(fields, fn field ->
        field["is_positional"] == false and is_binary(field["name"]) and
          Regex.match?(~r/^[A-Za-z_][A-Za-z0-9_]*$/, field["name"]) and
          field["attr_info"]["rename"] == nil
      end)
  end

  defp supported?(_, _), do: false

  def install!([], _translation, _output, _prefix), do: []

  def install!(plan, translation, output, prefix) do
    module = prefix <> ".NativeCodecs"
    path = Path.join(output, String.replace(module, ".", "/") <> ".lean")

    case File.read(path) do
      {:ok, "-- Generated by Lynx:" <> _} -> :ok
      {:error, :enoent} -> :ok
      _ -> raise ArgumentError, "refusing to overwrite a user Lean module: #{path}"
    end

    definitions = Enum.map_join(plan, "\n", &definition!(&1, translation))

    File.write!(path, """
    -- Generated by Lynx: lossless native heap codecs for extracted structs.
    module
    public import #{prefix}.Types
    public section
    open Lynx
    namespace #{module}
    #{definitions}
    end #{module}
    """)

    funs = Path.join(output, String.replace(prefix, ".", "/") <> "/Funs.lean")
    marker = "public import #{prefix}.Types"
    source = File.read!(funs)

    unless String.contains?(source, marker),
      do: raise(ArgumentError, "missing generated Types import")

    source = String.replace(source, marker, marker <> "\npublic import " <> module)
    source = Lynx.Rust.NativeOwnedDrops.install_instances!(plan, translation, source)
    File.write!(funs, source)
    [module]
  end

  defp definition!(type, translation) do
    id = type["def_id"]

    case Enum.filter(translation["types"], &(&1["def_id"] == id)) do
      [%{"lean_name" => lean, "rust_name" => rust}] ->
        expected = nominal!(type)

        unless rust == expected,
          do: raise(ArgumentError, "native heap type correspondence mismatch: #{id}")

        # The Rust nominal name comes from the audited extraction. The Lean
        # constructor and field types are independently checked by elaboration.
        names = Enum.with_index(type["kind"]["Struct"])

        encoded =
          Enum.map_join(names, ", ", fn {field, _} ->
            "NativeCodec.encode value.#{quote!(field["name"])}"
          end)

        pattern =
          Enum.reduce(Enum.reverse(names), ".nil", fn {_, i}, rest ->
            ".cons field#{i} (#{rest})"
          end)

        decoded =
          Enum.map_join(names, "\n        ", fn {_, i} ->
            "let value#{i} ← NativeCodec.decode field#{i}"
          end)

        fields =
          Enum.map_join(names, ", ", fn {field, i} -> "#{quote!(field["name"])} := value#{i}" end)

        """
        instance : NativeCodec #{identifier!(lean)} where
          typeName := #{JSON.encode!(type.native_tag)}
          encode value := .cons (.atom #{JSON.encode!(type.native_tag)}) (Term.list [#{encoded}])
          decode
            | .cons (.atom actualTag) (#{pattern}) =>
              if actualTag == #{JSON.encode!(type.native_tag)} then do
                #{decoded}
                return { #{fields} }
              else none
            | _ => none
          decode_encode value := by
            cases value
            simp [NativeCodec.roundtrip]

        #{if type.native_cleanup == :trivial, do: "instance : NativeResourceCleanup #{identifier!(lean)} where\n  cleanup _ := .ok ()\n  observable := false", else: ""}

        @[simp] theorem #{quote!("typeName::" <> rust)} :
            NativeCodec.typeName (α := #{identifier!(lean)}) = #{JSON.encode!(type.native_tag)} := rfl
        """

      _ ->
        raise ArgumentError, "missing or ambiguous native heap type correspondence: #{id}"
    end
  end

  # Exact names and recursively expanded field shapes, never extraction-local IDs.
  # A changed layout cannot decode a cell from a different extraction context.
  defp schema!(type, audit, types) do
    [
      nominal!(type),
      Enum.map(type["kind"]["Struct"], fn field ->
        value = schema_type!(field["ty"], audit, types)

        [field["name"], value]
      end)
    ]
  end

  defp schema_type!(type, audit, types) do
    case CallModels.expand(type, audit.references) do
      %{"Scalar" => "Bool"} ->
        "bool"

      %{"Scalar" => %{"Integer" => %{"Unsigned" => width}}} ->
        String.downcase(width)

      %{"Adt" => %{"id" => id, "generics" => %{"types" => [payload]}}} ->
        declaration = Enum.find(audit.translated["type_decls"], &(&1 && &1["def_id"] == id))

        unless Lynx.Rust.MutexModels.type?(declaration),
          do: raise(ArgumentError, "unsupported heap handle schema")

        ["std::sync::Mutex", schema_type!(payload, audit, types)]

      %{"Adt" => %{"id" => id}} ->
        cond do
          file_capability?(id, audit) -> "std::fs::File:borrowed-capability-v1"
          error_capability?(id, audit) -> "core::io::error::Error:os-capability-v1"
          true -> schema!(Map.fetch!(types, id), audit, types)
        end
    end
  end

  # FileModels/FileDrops emit this identity only after validating the standard
  # type and an admitted file operation/destruction. Other opaque types remain rejected.
  defp file_capability?(id, audit) do
    Lynx.Rust.FileModels.file_type?(audit.translated, id) and
      Enum.any?(audit.external_calls, fn
        {_, %{native_file_types: {^id, _}}} -> true
        _ -> false
      end)
  end

  defp error_capability?(id, audit) do
    Lynx.Rust.FileModels.error_type?(audit.translated, id) and
      Enum.any?(audit.external_calls, fn
        {_, %{native_io_error_drop: true, native_file_types: {_, ^id}}} -> true
        _ -> false
      end)
  end

  defp nominal!(type) do
    Enum.map_join(type["item_meta"]["name"], "::", fn
      %{"Ident" => [name, 0]} -> name
      _ -> raise ArgumentError, "unsupported nominal native heap type"
    end)
  end

  defp empty_parameters?(params),
    do:
      Enum.all?(
        ~w(regions types const_generics trait_clauses trait_type_constraints outlives),
        &(params[&1] == [])
      )

  defp identifier!(name), do: name |> String.split(".") |> Enum.map_join(".", &quote!/1)

  defp quote!(name) do
    if String.contains?(name, ["«", "»", "\n", "\r"]),
      do: raise(ArgumentError, "unsupported native codec identifier")

    "«" <> name <> "»"
  end
end
