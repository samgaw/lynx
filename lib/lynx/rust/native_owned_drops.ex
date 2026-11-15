defmodule Lynx.Rust.NativeOwnedDrops do
  @moduledoc false

  def function_for(payload, translated, refs), do: function_for(payload, translated, refs, [])

  defp function_for(payload, translated, refs, seen) do
    with true <- get_in(translated, ["options", "owned_drops"]) == true,
         payload = Lynx.Rust.CallModels.expand(payload, refs),
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args}} <- payload,
         true <- id not in seen,
         true <- args == Lynx.Rust.ResourceModels.args([]),
         type when not is_nil(type) <-
           Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id)),
         %{"src" => "Normal", "needs_drop" => true, "kind" => %{"Struct" => _}} <- type,
         true <- type["item_meta"]["opacity"] == "Transparent",
         true <- Enum.all?(Map.values(type["generics"]), &(&1 == [])),
         name = type["item_meta"]["name"] ++ [%{"Ident" => ["drop_owned", 0]}],
         [function] <-
           Enum.filter(translated["fun_decls"], &(&1 && &1["item_meta"]["name"] == name)),
         %{
           "body" => %{"Structured" => _},
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig
         } <- function,
         true <- Enum.all?(Map.values(function["generics"]), &(&1 == [])),
         true <- Lynx.Rust.CallModels.expand(sig["inputs"], refs) == [payload],
         %{"Adt" => %{"builtin" => "Tuple", "generics" => output}} <-
           Lynx.Rust.CallModels.expand(sig["output"], refs),
         true <- output == Lynx.Rust.ResourceModels.args([]),
         true <-
           structural_nonpanicking?(function, translated, refs, [id | seen]) do
      function
    else
      _ -> nil
    end
  end

  # Keep nested owning structs within the same finite structural fragment. Each
  # level requires its captured consuming helper; the actual nested DropGlue is
  # separately audited before its logical-heap erasure is accepted.
  def vector_cleanup_for(payload, translated, refs),
    do: vector_cleanup_for(payload, translated, refs, [])

  defp vector_cleanup_for(payload, translated, refs, seen) do
    with %{"Adt" => %{"id" => id}} <- Lynx.Rust.CallModels.expand(payload, refs),
         true <- id not in seen,
         %{"kind" => %{"Struct" => fields}} <-
           Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id)),
         kinds = Enum.map(fields, &field_kind(&1["ty"], translated, refs, [id | seen])),
         true <- :owning in kinds and :unsupported not in kinds do
      function_for(payload, translated, refs, seen)
    else
      _ -> nil
    end
  end

  defp field_kind(type, translated, refs, seen) do
    cond do
      vector?(type, translated, refs) -> :owning
      Lynx.Rust.NativeDrops.plain_data?(type, translated, refs) -> :plain
      vector_cleanup_for(type, translated, refs, seen) != nil -> :owning
      true -> :unsupported
    end
  end

  defp vector?(type, translated, refs),
    do: match?({:ok, _}, Lynx.Rust.CollectionModels.scalar_vector_element(type, translated, refs))

  # Resource drop dispatch is classified as cutoff-only by the lifetime audit.
  # Admit structural cleanup of validated nonpanicking mutex/File primitives or
  # exact scalar Vec/Global drops checked by the existing structural audit;
  # nested scalar-vector glue must pass the same audit and captured-helper check.
  # Observable custom destructor calls still need separate unwind composition.
  defp structural_nonpanicking?(function, translated, refs, seen) do
    statements = function["body"]["Structured"]["body"]["statements"]

    Enum.all?(statements, fn statement ->
      case statement["kind"] do
        kind when kind == "Return" ->
          true

        %{"StorageLive" => _} ->
          true

        %{"StorageDead" => _} ->
          true

        %{"Assign" => [_, value]} ->
          Enum.any?(~w(Use Aggregate), &Map.has_key?(value, &1))

        %{"Drop" => drop} ->
          # Check the primitive kind before consulting drop dictionaries. A
          # recursive ResourceArc field must not re-enter resource admission.
          if match?(
               {:ok, _},
               Lynx.Rust.CollectionModels.scalar_vector_element(
                 drop["place"]["ty"],
                 translated,
                 refs
               )
             ) do
            Lynx.Rust.DropModels.nonpanicking_site?(drop, function, translated, refs)
          else
            case vector_cleanup_for(drop["place"]["ty"], translated, refs, seen) do
              nil ->
                primitive_type?(drop["place"]["ty"], translated, refs) and
                  case Lynx.Rust.NativeDrops.site(drop, translated, refs) do
                    {:ok, %{native_kind: kind}} when kind in [:mutex, :file] -> true
                    _ -> false
                  end

              _helper ->
                crates = cleanup_crates(drop["place"]["ty"], translated, refs, [])
                Lynx.Rust.DropModels.nonpanicking_site?(drop, function, translated, refs, crates)
            end
          end

        %{
          "Call" => %{
            "call" => %{
              "func" => %{
                "Regular" => %{
                  "kind" => %{"Fun" => id},
                  "generics" => %{"types" => [self]} = args
                }
              }
            }
          }
        } ->
          function = Enum.find(translated["fun_decls"], &(&1 && &1["def_id"] == id))

          with %{"Adt" => %{"id" => type}} <- Lynx.Rust.CallModels.expand(self, refs),
               declaration <- Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == type)),
               true <- primitive_type?(self, translated, refs) do
            if Lynx.Rust.MutexModels.type?(declaration) do
              Lynx.Rust.NativeDrops.supported_mutex_payload?(self, translated, refs) and
                match?(
                  %{native_dispose: true},
                  Lynx.Rust.NativeDrops.resolve(function, translated, refs)
                )
            else
              Lynx.Rust.FileDrops.resolve(function, translated, refs) != nil and
                Lynx.Rust.FileDrops.call?(
                  args,
                  translated,
                  refs,
                  Lynx.Rust.ResourceModels.trait_references(translated)
                )
            end
          else
            _ -> false
          end

        _ ->
          false
      end
    end)
  end

  # This is called only after the complete field tree has passed admission.
  # Include its crates so the existing audit follows actual nested DropGlue
  # across crate boundaries rather than treating it as an external model.
  defp cleanup_crates(type, translated, refs, seen) do
    case Lynx.Rust.CallModels.expand(type, refs) do
      %{"Adt" => %{"id" => id}} ->
        if id in seen do
          []
        else
          case Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id)) do
            %{
              "kind" => %{"Struct" => fields},
              "src" => "Normal",
              "item_meta" => %{"name" => [%{"Ident" => [crate, _]} | _]}
            } ->
              [
                crate
                | Enum.flat_map(fields, &cleanup_crates(&1["ty"], translated, refs, [id | seen]))
              ]
              |> Enum.uniq()

            _ ->
              []
          end
        end

      _ ->
        []
    end
  end

  defp primitive_type?(type, translated, refs) do
    case Lynx.Rust.CallModels.expand(type, refs) do
      %{"Adt" => %{"id" => id}} ->
        Lynx.Rust.MutexModels.type?(
          Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id))
        ) or Lynx.Rust.FileModels.file_type?(translated, id)

      _ ->
        false
    end
  end

  # Insert a concrete dictionary immediately after the actual Aeneas declaration.
  # No default dictionary exists for a dropful resource. Order or formatting changes
  # fail closed instead of silently using the old destructor-free release path.
  def install_instances!(plan, translation, source) do
    Enum.reduce(plan, source, fn type, source ->
      if is_integer(type.native_cleanup) do
        {mapping, typename} =
          case {Enum.filter(translation["functions"], &(&1["def_id"] == type.native_cleanup)),
                Enum.filter(translation["types"], &(&1["def_id"] == type["def_id"]))} do
            {[mapping], [typename]} -> {mapping, typename}
            _ -> raise ArgumentError, "missing or ambiguous owning cleanup correspondence"
          end

        if mapping["is_opaque"] or mapping["is_rec"],
          do: raise(ArgumentError, "unsupported owning destructor declaration")

        marker = "/-- [#{mapping["rust_name"]}]:"

        case String.split(source, marker) do
          [before, body] ->
            case Regex.run(~r/\n(?=\/--|end |namespace )/, body, return: :index) do
              [{offset, _}] ->
                {definition, rest} = String.split_at(body, offset)

                dictionary =
                  "\ninstance : Lynx.NativeResourceCleanup #{typename["lean_name"]} where\n  cleanup := #{mapping["lean_name"]}\n" <>
                    "\ninstance : Lynx.NativeMutexDrop #{typename["lean_name"]} where\n  drop := Lynx.NativeMutex.disposeWith #{mapping["lean_name"]}\n"

                before <> marker <> definition <> dictionary <> rest

              _ ->
                raise ArgumentError, "missing owning destructor declaration boundary"
            end

          _ ->
            raise ArgumentError, "missing or ambiguous emitted owning destructor"
        end
      else
        source
      end
    end)
  end

  def arguments!(false, _), do: []
  def arguments!(:explicit, _), do: ["--precise-drops", "--desugar-drops"]

  def arguments!(true, tools) do
    versions = File.read!(Path.join(tools, "lynx-toolchain")) |> String.split("\n")

    unless Enum.any?(
             versions,
             &(String.starts_with?(&1, "charon=") and "owned-drops-v1" in String.split(&1, "+"))
           ),
           do:
             raise(ArgumentError, "owned destruction requires the pinned owned-drops-v1 compiler")

    ["--owned-drops"]
  end

  def arguments!(other, _),
    do: raise(ArgumentError, "invalid owned_drops option: #{inspect(other)}")
end
