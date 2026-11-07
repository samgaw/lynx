defmodule Lynx.Rust.FileModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, LLBC}
  @file_path ~w(std fs File)
  @error ~w(core io error Error)
  @seek ~w(core io seek SeekFrom)

  def enabled!(:reject, _execution), do: []
  def enabled!(:regular, :runtime), do: [:native_files]

  def enabled!(:regular, _),
    do: raise(ArgumentError, "regular-file models require runtime execution")

  def enabled!(other, _),
    do: raise(ArgumentError, "unsupported Rust file model: #{inspect(other)}")

  def resolve(function, translated, refs),
    do:
      resolve_shared_write(function, translated, refs) ||
        resolve_direct(function, translated, refs)

  defp resolve_direct(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "generics" => params
         } <- function,
         file when not is_nil(file) <- type(translated, @file_path),
         error when not is_nil(error) <- type(translated, @error),
         regions when is_list(regions) <- params["regions"],
         true <- plain?(params, length(regions)) do
      f = adt(file["def_id"])
      e = adt(error["def_id"])
      input = CallModels.expand(sig["inputs"], refs)
      output = CallModels.expand(sig["output"], refs)

      selected =
        cond do
          length(params["regions"]) == 2 and
            input == [
              reference(0, f, "Mut"),
              reference(1, %{"Slice" => [scalar("U8"), nil]}, "Shared")
            ] and
            result?(output, scalar("Usize"), e, translated, refs) and
              io_method?(function, f, translated, refs, "write", ~w(core io write Write)) ->
            {"std::fs::{core::io::write::Write<std::fs::File>}::write", "write"}

          length(params["regions"]) == 2 and
            input == [
              reference(0, f, "Mut"),
              reference(1, %{"Slice" => [scalar("U8"), nil]}, "Mut")
            ] and result?(output, scalar("Usize"), e, translated, refs) and
              io_method?(function, f, translated, refs, "read", ~w(alloc io read Read)) ->
            {"std::fs::{alloc::io::read::Read<std::fs::File>}::read", "read"}

          length(params["regions"]) == 1 and seek_type?(translated, refs) and
            input == [reference(0, f, "Mut"), adt(seek_id(translated))] and
            result?(output, scalar("U64"), e, translated, refs) and
              io_method?(function, f, translated, refs, "seek", ~w(core io seek Seek)) ->
            {"std::fs::{core::io::seek::Seek<std::fs::File>}::seek", "seek"}

          length(params["regions"]) == 1 and input == [reference(0, f, "Shared")] and
            result?(
              output,
              %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => args([])}},
              e,
              translated,
              refs
            ) and
              inherent?(function, f, refs, "sync_all") ->
            {"std::fs::{std::fs::File}::sync_all", "syncAll"}

          length(params["regions"]) == 1 and input == [reference(0, f, "Shared"), scalar("U64")] and
            result?(
              output,
              %{"Adt" => %{"id" => 0, "builtin" => "Tuple", "generics" => args([])}},
              e,
              translated,
              refs
            ) and inherent?(function, f, refs, "set_len") ->
            {"std::fs::{std::fs::File}::set_len", "setLen"}

          true ->
            nil
        end

      if selected do
        {rust, lean} = selected

        %{
          rust_name: rust,
          lean: "Lynx.NativeFile." <> lean,
          builtin: false,
          can_fail: true,
          lift: true,
          native_cutoff_only: true,
          native_file_types: {file["def_id"], error["def_id"]},
          file_seek_type: if(lean == "seek", do: seek_id(translated), else: nil),
          label:
            "Bounded regular-file #{lean} model (1048576 bytes): registered borrowed file identities, explicit partial/error outcomes; write errors preserve visible bytes and offset while retaining permitted background persistence (std/OS model assumption); reads preserve unread buffer bytes and preserve the buffer/offset on errors (std/OS model assumptions); bytewise old/new torn persistence with length between durable and visible sizes; set_len changes visible length, preserves offset and zero-fills extension; successful set_len does not guarantee persistence; failed set_len preserves visible length and bytes (std/OS assumption); regular-file sync_all success persists visible contents and length; admitted root-directory sync_all success commits visible namespace names without synchronizing inode bytes, with filesystem/device correspondence assumed; directory sync errors retain the last guaranteed checkpoint; seek computes the bounded signed target, preserves contents, and preserves the offset on errors (std/OS assumption); single-file and bounded flat-filesystem crash-image/restart host admission, per-path metadata-version choices, std, OS, filesystem/device and native descriptor correspondence unverified; open/append modes and unrestricted concurrent file access unsupported; owned File destruction requires the separately validated close model; synchronized callers may be verified against these per-operation transitions"
        }
      end
    else
      _ -> nil
    end
  end

  # Write for &File mutably borrows the reference slot, not an owned File.
  # Validate its inherited lifetime and actual trait-method substitution; the
  # existing write primitive reconstructs the same file identity after the call.
  defp resolve_shared_write(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "generics" => params,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["std", 0]},
               %{"Ident" => ["fs", 0]},
               %{"Impl" => %{"Trait" => impl_id}},
               %{"Ident" => ["write", 0]}
             ]
           },
           "src" => %{"TraitImpl" => %{"trait_ref" => %{"id" => trait}}}
         } <- function,
         file when not is_nil(file) <- type(translated, @file_path),
         error when not is_nil(error) <- type(translated, @error),
         true <- plain?(%{params | "outlives" => []}, 3),
         true <- Enum.map(params["regions"], & &1["index"]) == [0, 1, 2],
         true <-
           params["outlives"] == [
             %{
               "regions" => [],
               "outlives" => [],
               "skip_binder" => [%{"Var" => %{"Free" => 0}}, %{"Var" => %{"Free" => 1}}]
             }
           ],
         f = adt(file["def_id"]),
         shared = reference(0, f, "Shared"),
         true <-
           CallModels.expand(sig["inputs"], refs) == [
             reference(1, shared, "Mut"),
             reference(2, %{"Slice" => [scalar("U8"), nil]}, "Shared")
           ],
         true <-
           result?(
             CallModels.expand(sig["output"], refs),
             scalar("Usize"),
             adt(error["def_id"]),
             translated,
             refs
           ),
         %{
           "src" => "Normal",
           "is_unsafe" => false,
           "is_negative" => false,
           "generics" => impl_params,
           "methods" => methods
         } = impl <-
           Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == impl_id)),
         true <- plain?(impl_params, 1) and Enum.map(impl_params["regions"], & &1["index"]) == [0],
         true <- impl["item_meta"]["name"] == Enum.take(function["item_meta"]["name"], 3),
         true <-
           CallModels.expand(impl["impl_trait"], refs) == %{
             "id" => trait,
             "generics" => args([shared])
           },
         %{"item_meta" => %{"name" => trait_name}} <-
           Enum.find(translated["trait_decls"], &(&1 && &1["def_id"] == trait)),
         true <- trait_name == name(~w(core io write Write)),
         selected =
           Enum.filter(methods, &match?(%{"kind" => %{"TraitMethod" => [^trait, 0]}}, &1)),
         true <-
           Lynx.Rust.FormatModels.method_identity?(
             function,
             %{impl | "methods" => selected},
             trait,
             %{translated: translated, refs: refs}
           ) do
      %{
        rust_name: "std::fs::{core::io::write::Write<&'0 std::fs::File>}::write",
        lean: "Lynx.NativeFile.write",
        builtin: false,
        can_fail: true,
        lift: true,
        native_cutoff_only: true,
        native_file_types: {file["def_id"], error["def_id"]},
        file_seek_type: nil,
        label:
          "Bounded shared File write model (1048576 bytes): exact standard Write<&File> identity, inherited lifetime and method substitution validated; preserves the borrowed file identity; delegates to the existing partial-write, offset, permission and background-persistence transition; std/OS/descriptor/FFI correspondence unverified; open/append flags and unrestricted concurrent writes unsupported"
      }
    else
      _ -> nil
    end
  end

  def declaration(translated), do: type(translated, @file_path)

  def error_declaration(translated), do: type(translated, @error)

  def error_type?(translated, id) do
    case error_declaration(translated) do
      %{"def_id" => ^id} -> true
      _ -> false
    end
  end

  def file_type?(translated, id) do
    case type(translated, @file_path) do
      %{"def_id" => ^id} -> true
      _ -> false
    end
  end

  def scope(audit, prefix) do
    calls =
      Map.new(audit.external_calls, fn {id, model} ->
        if model[:file_seek_type],
          do: {id, %{model | lean: prefix <> ".FileModel.seek"}},
          else: {id, model}
      end)

    %{audit | external_calls: calls}
  end

  def install!(audit, translation, output, prefix) do
    ids =
      audit.external_calls
      |> Map.values()
      |> Enum.map(& &1[:file_seek_type])
      |> Enum.reject(&is_nil/1)
      |> Enum.uniq()

    case ids do
      [] ->
        []

      [id] ->
        [type] = Enum.filter(translation["types"], &(&1["def_id"] == id))

        unless type["rust_name"] == Enum.join(@seek, "::"),
          do: raise(ArgumentError, "file seek type correspondence mismatch")

        module = prefix <> ".FileModel"
        path = Path.join(output, String.replace(module, ".", "/") <> ".lean")

        case File.read(path) do
          {:ok, "-- Generated by Lynx:" <> _} -> :ok
          {:error, :enoent} -> :ok
          _ -> raise ArgumentError, "refusing to overwrite a user Lean module: #{path}"
        end

        File.mkdir_p!(Path.dirname(path))

        File.write!(path, """
        -- Generated by Lynx: checked standard SeekFrom conversion.
        module
        public import #{prefix}.Types
        public section
        open Aeneas Aeneas.Std Lynx
        namespace #{module}
        @[expose] def seek (file : NativeFile) (origin : #{type["lean_name"]}) :
            NativeM (core.result.Result U64 NativeIoError × NativeFile) :=
          NativeFile.seek file (match origin with
            | .Start offset => .start offset
            | .End offset => .end_ offset
            | .Current offset => .current offset)
        end #{module}
        """)

        funs = Path.join(output, String.replace(prefix, ".", "/") <> "/Funs.lean")
        marker = "public import #{prefix}.Types"
        source = File.read!(funs)

        unless String.contains?(source, marker),
          do: raise(ArgumentError, "missing generated Types import")

        File.write!(funs, String.replace(source, marker, marker <> "\npublic import " <> module))
        [module]
    end
  end

  defp seek_id(translated) do
    case Enum.filter(translated["type_decls"], &(&1 && &1["item_meta"]["name"] == name(@seek))) do
      [type] -> type["def_id"]
      _ -> nil
    end
  end

  defp seek_type?(translated, refs) do
    id = seek_id(translated)

    case id && Enum.find(translated["type_decls"], &(&1 && &1["def_id"] == id)) do
      %{"src" => "Normal", "generics" => params, "kind" => %{"Enum" => variants}} ->
        plain?(params, 0) and
          Enum.map(variants, fn variant ->
            {variant["id"], variant["name"],
             Enum.map(variant["fields"], &CallModels.expand(&1["ty"], refs)),
             variant["discriminant"]}
          end) == [
            {0, "Start", [scalar("U64")], %{"Signed" => ["Isize", "0"]}},
            {1, "End", [signed("I64")], %{"Signed" => ["Isize", "1"]}},
            {2, "Current", [signed("I64")], %{"Signed" => ["Isize", "2"]}}
          ]

      _ ->
        false
    end
  end

  def type_models(calls, prefix) do
    if Enum.any?(calls, fn {_, model} -> model[:native_file_types] != nil end) do
      errors =
        Enum.any?(calls, fn {_, model} ->
          match?({_, id} when is_integer(id), model[:native_file_types])
        end)

      files =
        Enum.any?(calls, fn {_, model} ->
          match?({id, _} when is_integer(id), model[:native_file_types])
        end)

      for {rust, lean} <-
            if(files, do: [{@file_path, "Lynx.NativeFile"}], else: []) ++
              if(errors, do: [{@error, "Lynx.NativeIoError"}], else: []) do
        %{
          rust: Enum.join(rust, "::"),
          lean: lean,
          import: (prefix |> String.split(".") |> hd()) <> ".NativeRuntime",
          label:
            "Registered regular-file capability or opaque I/O error identity; optional error destruction requires a separate unique live callback-free OS-error capability; physical descriptors, error payload reclamation, std/allocator cleanup and OS correspondence unverified"
        }
      end
    else
      []
    end
  end

  defp type(translated, path) do
    case Enum.filter(translated["type_decls"], &(&1 && &1["item_meta"]["name"] == name(path))) do
      [%{"src" => "Normal", "kind" => "Opaque", "generics" => params} = type] ->
        if plain?(params, 0), do: type

      _ ->
        nil
    end
  end

  defp io_method?(
         %{
           "def_id" => id,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["std", 0]},
               %{"Ident" => ["fs", 0]},
               %{"Impl" => %{"Trait" => impl}},
               %{"Ident" => [method, 0]}
             ]
           },
           "src" => %{
             "TraitImpl" => %{
               "impl_ref" => %{"id" => impl},
               "trait_ref" => %{"id" => trait},
               "item_id" => 0,
               "reuses_default" => false
             }
           }
         },
         file,
         translated,
         refs,
         method,
         trait_path
       ) do
    with %{
           "src" => "Normal",
           "is_negative" => false,
           "is_unsafe" => false,
           "generics" => params,
           "impl_trait" => %{"id" => ^trait, "generics" => generics},
           "methods" => methods
         } <- Enum.find(translated["trait_impls"], &(&1 && &1["def_id"] == impl)),
         true <- plain?(params, 0),
         true <- CallModels.expand(generics, refs) == args([file]),
         %{"item_meta" => %{"name" => trait_name}} <-
           Enum.find(translated["trait_decls"], &(&1 && &1["def_id"] == trait)) do
      trait_name == name(trait_path) and
        Enum.any?(methods, fn
          %{"kind" => %{"TraitMethod" => [^trait, 0]}, "skip_binder" => %{"id" => ^id}} -> true
          _ -> false
        end)
    else
      _ -> false
    end
  end

  defp io_method?(_, _, _, _, _, _), do: false

  defp inherent?(
         %{
           "src" => "Normal",
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["std", 0]},
               %{"Ident" => ["fs", 0]},
               %{
                 "Impl" => %{
                   "Ty" => %{
                     "kind" => "InherentImplBlock",
                     "params" => params,
                     "skip_binder" => parent
                   }
                 }
               },
               %{"Ident" => [method, 0]}
             ]
           }
         },
         file,
         refs,
         method
       ),
       do: plain?(params, 0) and CallModels.expand(parent, refs) == file

  defp inherent?(_, _, _, _), do: false

  defp result?(
         %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => generics}},
         ok,
         error,
         translated,
         refs
       ),
       do:
         generics == args([ok, error]) and
           LLBC.result_type?(id, %{translated: translated, references: refs})

  defp result?(_, _, _, _, _), do: false

  defp plain?(p, regions),
    do:
      p["types"] == [] and p["const_generics"] == [] and p["trait_clauses"] == [] and
        p["trait_type_constraints"] == [] and p["outlives"] == [] and
        is_list(p["regions"]) and length(p["regions"]) == regions

  defp name(parts), do: Enum.map(parts, &%{"Ident" => [&1, 0]})

  defp args(types),
    do: %{"types" => types, "regions" => [], "const_generics" => [], "trait_refs" => []}

  defp adt(id), do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => args([])}}
  defp scalar(type), do: %{"Scalar" => %{"Integer" => %{"Unsigned" => type}}}
  defp signed(type), do: %{"Scalar" => %{"Integer" => %{"Signed" => type}}}
  defp reference(index, type, kind), do: %{"Ref" => [%{"Var" => %{"Free" => index}}, type, kind]}
end
