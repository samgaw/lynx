defmodule Lynx.Rust.NativeCodecs do
  @moduledoc false
  alias Lynx.Rust.CallModels

  # Only actual monomorphic first-party structs and plain-data enums are derived.
  # NativeCodec is an internal lossless heap representation, never a Rustler codec.
  def plan!(audit) do
    constructors =
      for {id, model} <- audit.external_calls,
          model[:native_constructor] == true or model[:native_codec_input] == true or
            model[:native_codec_owned_input] == true or
            model[:native_codec_drop] == true or model[:resource_operation] != nil,
          into: %{},
          do:
            {id,
             cond do
               model[:resource_operation] -> :resource
               model[:native_codec_owned_input] -> :owned
               model[:native_codec_drop] -> :drop
               true -> model[:native_codec_input] == true
             end}

    roots = Enum.flat_map(audit.functions, &payloads(&1["body"], constructors, audit.references))
    plan = Enum.reduce(roots, [], &visit!(&1, audit, &2, []))

    Enum.map(plan, fn type ->
      schema = schema!(type, audit, Map.new(plan, &{&1["def_id"], &1}))

      cleanup =
        if Lynx.Rust.ResourceLifetimes.enabled?(audit.translated) or
             Lynx.Rust.ResourceLifetimes.logical_payload?(
               type,
               audit.translated,
               audit.references
             ) do
          {:logical, Lynx.Rust.ResourceLifetimes.cleanup_fields!(type, audit)}
        else
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
        end

      type |> Map.put(:native_tag, JSON.encode!(schema)) |> Map.put(:native_cleanup, cleanup)
    end)
  end

  defp payloads(%{"Regular" => %{"kind" => %{"Fun" => id}, "generics" => generics}}, ids, refs) do
    case {Map.fetch(ids, id), generics} do
      {{:ok, :owned},
       %{"types" => [type], "regions" => [], "const_generics" => [], "trait_refs" => []}} ->
        [type]

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
      %{"Array" => [element, _, _]} = array ->
        unless Lynx.Rust.NativeDrops.plain_data?(array, audit.translated, audit.references),
          do: raise(ArgumentError, "unsupported native array length or element ownership")

        visit!(element, audit, found, visiting)

      %{"Scalar" => "Bool"} ->
        found

      %{"Scalar" => %{"Integer" => %{"Unsigned" => width}}}
      when width in ~w(U8 U16 U32 U64 U128 Usize) ->
        found

      %{"Scalar" => %{"Integer" => %{"Signed" => width}}}
      when width in ~w(I8 I16 I32 I64 I128 Isize) ->
        found

      %{"Adt" => %{"generics" => %{"types" => [_, _, _]}}} = collection ->
        unless Lynx.Rust.OrderedCollectionModels.supported_family(
                 collection,
                 audit.translated,
                 audit.references
               ) == "map",
               do: raise(ArgumentError, "unsupported native ordered map representation")

        found

      %{"Adt" => %{"generics" => %{"types" => [_, _]}}} = atomic ->
        unless not is_nil(
                 Lynx.Rust.AtomicModels.supported?(atomic, audit.translated, audit.references)
               ) or
                 Lynx.Rust.OrderedCollectionModels.supported_family(
                   atomic,
                   audit.translated,
                   audit.references
                 ) == "set",
               do:
                 raise(
                   ArgumentError,
                   "unsupported atomic heap handle identity or ordered set representation"
                 )

        found

      %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => %{"types" => [payload]} = args}} =
          self ->
        type = Enum.find(audit.translated["type_decls"], &(&1 && &1["def_id"] == id))

        vector =
          (get_in(audit.translated, ["options", "owned_drops"]) == true or
             (match?(%{global_vectors: true}, audit[:allocator_layout]) and
                Lynx.Rust.CollectionModels.scalar_vector_element(
                  self,
                  audit.translated,
                  audit.references
                ) == {:ok, %{"Scalar" => %{"Integer" => %{"Unsigned" => "U8"}}}})) and
            match?(
              {:ok, _},
              Lynx.Rust.CollectionModels.scalar_vector_element(
                self,
                audit.translated,
                audit.references
              )
            )

        unless vector or
                 ((Lynx.Rust.MutexModels.type?(type) or Lynx.Rust.RwLockModels.type?(type)) and
                    args == Lynx.Rust.ResourceModels.args([payload])),
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

            unless supported?(declaration, audit),
              do:
                raise(
                  ArgumentError,
                  "unsupported native heap struct identity or unsupported plain-data enum #{id}"
                )

            found =
              Enum.reduce(
                fields!(declaration),
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
         %{first_party: first_party}
       ) do
    crate in first_party and empty_parameters?(params) and
      attrs["rename"] == nil and
      Enum.all?(fields, fn field ->
        field["is_positional"] == false and is_binary(field["name"]) and
          Regex.match?(~r/^[A-Za-z_][A-Za-z0-9_]*$/, field["name"]) and
          field["attr_info"]["rename"] == nil
      end)
  end

  defp supported?(
         %{
           "generics" => params,
           "needs_drop" => false,
           "kind" => %{"Enum" => variants},
           "item_meta" => %{"name" => [%{"Ident" => [crate, 0]} | _], "attr_info" => attrs}
         },
         %{first_party: first_party} = audit
       )
       when is_list(variants) and variants != [] do
    crate in first_party and empty_parameters?(params) and attrs["rename"] == nil and
      length(Enum.uniq_by(variants, & &1["name"])) == length(variants) and
      Enum.all?(Enum.with_index(variants), fn {variant, index} ->
        variant["id"] == index and identifier?(variant["name"]) and
          variant["attr_info"]["rename"] == nil and is_list(variant["fields"]) and
          enum_fields?(variant["fields"], audit)
      end)
  end

  defp supported?(_, _), do: false

  defp enum_fields?(fields, audit) do
    length(Enum.uniq_by(fields, & &1["name"])) == length(fields) and
      length(Enum.uniq(Enum.map(fields, & &1["is_positional"]))) <= 1 and
      Enum.all?(Enum.with_index(fields), fn {field, index} ->
        identifier?(field["name"]) and field["is_positional"] in [true, false] and
          (field["is_positional"] == false or field["name"] == "_#{index}") and
          field["attr_info"]["rename"] == nil and
          Lynx.Rust.NativeDrops.plain_data?(field["ty"], audit.translated, audit.references)
      end)
  end

  defp identifier?(name),
    do: is_binary(name) and Regex.match?(~r/^[A-Za-z_][A-Za-z0-9_]*$/, name)

  defp fields!(%{"kind" => %{"Struct" => fields}}), do: fields
  defp fields!(%{"kind" => %{"Enum" => variants}}), do: Enum.flat_map(variants, & &1["fields"])

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
    -- Generated by Lynx: lossless native heap codecs for extracted first-party types.
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
        if variants = type["kind"]["Enum"] do
          enum_definition!(type, lean, rust, variants)
        else
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
            Enum.map_join(names, ", ", fn {field, i} ->
              "#{quote!(field["name"])} := value#{i}"
            end)

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

          #{cleanup_definition(type.native_cleanup, identifier!(lean))}

          @[simp] theorem #{quote!("typeName::" <> rust)} :
              NativeCodec.typeName (α := #{identifier!(lean)}) = #{JSON.encode!(type.native_tag)} := rfl
          """
        end

      _ ->
        raise ArgumentError, "missing or ambiguous native heap type correspondence: #{id}"
    end
  end

  defp enum_definition!(type, lean, rust, variants) do
    encoded =
      Enum.map_join(variants, "\n", fn variant ->
        values = for {_field, i} <- Enum.with_index(variant["fields"]), do: "value#{i}"
        terms = Enum.map_join(values, ", ", &("NativeCodec.encode " <> &1))

        "| .#{quote!(variant["name"])} #{Enum.join(values, " ")} => .cons (.atom #{JSON.encode!(type.native_tag)}) (.cons (.atom #{JSON.encode!(variant["name"])}) (Term.list [#{terms}]))"
      end)

    decoded =
      Enum.map_join(variants, "\n", fn variant ->
        names = Enum.with_index(variant["fields"])

        pattern =
          Enum.reduce(Enum.reverse(names), ".nil", fn {_, i}, rest ->
            ".cons field#{i} (#{rest})"
          end)

        fields =
          Enum.map_join(names, "\n    ", fn {_, i} ->
            "let value#{i} ← NativeCodec.decode field#{i}"
          end)

        values = Enum.map_join(names, " ", fn {_, i} -> "value#{i}" end)

        """
        | .cons (.atom actualTag) (.cons (.atom #{JSON.encode!(variant["name"])}) (#{pattern})) =>
          if actualTag == #{JSON.encode!(type.native_tag)} then do
            #{fields}
            return .#{quote!(variant["name"])} #{values}
          else none
        """
      end)

    encoded = String.replace(encoded, "\n", "\n    ")
    decoded = String.replace(decoded, "\n", "\n    ")

    """
    instance : NativeCodec #{identifier!(lean)} where
      typeName := #{JSON.encode!(type.native_tag)}
      encode value := match value with
        #{encoded}
      decode
        #{decoded}
        | _ => none
      decode_encode value := by
        cases value <;> simp [NativeCodec.roundtrip]

    #{cleanup_definition(type.native_cleanup, identifier!(lean))}

    @[simp] theorem #{quote!("typeName::" <> rust)} :
        NativeCodec.typeName (α := #{identifier!(lean)}) = #{JSON.encode!(type.native_tag)} := rfl
    """
  end

  defp cleanup_definition(:trivial, lean),
    do:
      "instance : NativeResourceCleanup #{lean} where\n  cleanup _ := .ok ()\n  observable := false\n" <>
        "instance : Lynx.NativeMutexDrop #{lean} where\n  drop := Lynx.NativeMutex.dispose\n"

  defp cleanup_definition({:logical, []}, lean), do: cleanup_definition(:trivial, lean)

  defp cleanup_definition({:logical, fields}, lean) do
    calls =
      Enum.map_join(fields, "\n    ", fn {field, operation} ->
        "#{operation} value.#{quote!(field)}"
      end)

    "instance : NativeResourceCleanup #{lean} where\n  cleanup value := do\n    #{calls}\n    return ()\n  observable := false\n" <>
      "instance : Lynx.NativeMutexDrop #{lean} where\n" <>
      "  drop := Lynx.NativeMutex.disposeWith (NativeResourceCleanup.cleanup (α := #{lean}))\n"
  end

  defp cleanup_definition(_, _), do: ""

  # Exact names and recursively expanded field shapes, never extraction-local IDs.
  # A changed layout cannot decode a cell from a different extraction context.
  defp schema!(type, audit, types) do
    fields = fn fields ->
      Enum.map(fields, fn field -> [field["name"], schema_type!(field["ty"], audit, types)] end)
    end

    layout =
      case type["kind"] do
        %{"Struct" => entries} ->
          fields.(entries)

        %{"Enum" => variants} ->
          [
            "enum",
            Enum.map(variants, fn variant ->
              [
                variant["name"],
                variant["discriminant"],
                Enum.map(variant["fields"], fn field ->
                  [field["name"], field["is_positional"], schema_type!(field["ty"], audit, types)]
                end)
              ]
            end)
          ]
      end

    [nominal!(type), layout]
  end

  defp schema_type!(type, audit, types) do
    case CallModels.expand(type, audit.references) do
      %{"Array" => [element, _, _]} = array ->
        {:ok, length} = Lynx.Rust.NativeDrops.array_length(array)
        ["array", length, schema_type!(element, audit, types)]

      %{"Scalar" => "Bool"} ->
        "bool"

      %{"Scalar" => %{"Integer" => %{"Unsigned" => width}}} ->
        String.downcase(width)

      %{"Scalar" => %{"Integer" => %{"Signed" => width}}}
      when width in ~w(I8 I16 I32 I64 I128 Isize) ->
        String.downcase(width)

      %{"Adt" => %{"generics" => %{"types" => [_, _, _]}}} = collection ->
        unless Lynx.Rust.OrderedCollectionModels.supported_family(
                 collection,
                 audit.translated,
                 audit.references
               ) == "map",
               do: raise(ArgumentError, "unsupported ordered map heap schema")

        "alloc::collections::BTreeMap<u64,u64>:ordered-v1"

      %{"Adt" => %{"generics" => %{"types" => [_, _]}}} = atomic ->
        cond do
          Lynx.Rust.AtomicModels.supported?(atomic, audit.translated, audit.references) ->
            "core::sync::atomic::AtomicU64:seqcst-v1"

          Lynx.Rust.OrderedCollectionModels.supported_family(
            atomic,
            audit.translated,
            audit.references
          ) == "set" ->
            "alloc::collections::BTreeSet<u64>:ordered-v1"

          true ->
            raise ArgumentError,
                  "unsupported atomic heap handle schema or ordered set representation"
        end

      %{"Adt" => %{"id" => id, "generics" => %{"types" => [payload]}}} = self ->
        declaration = Enum.find(audit.translated["type_decls"], &(&1 && &1["def_id"] == id))

        vector =
          match?(
            {:ok, _},
            Lynx.Rust.CollectionModels.scalar_vector_element(
              self,
              audit.translated,
              audit.references
            )
          )

        unless vector or Lynx.Rust.MutexModels.type?(declaration) or
                 Lynx.Rust.RwLockModels.type?(declaration),
               do: raise(ArgumentError, "unsupported heap handle schema")

        name =
          cond do
            vector -> "alloc::vec::Vec"
            Lynx.Rust.MutexModels.type?(declaration) -> "std::sync::Mutex"
            true -> "std::sync::RwLock"
          end

        [name, schema_type!(payload, audit, types)]

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
