defmodule Lynx.Rust.IoErrorModels do
  @moduledoc false
  alias Lynx.Rust.{CallModels, FileModels, ResourceModels}
  @kind ~w(core io error ErrorKind)

  def resolve(function, translated, refs) do
    resolve_borrowed(function, translated, refs) || resolve_static(function, translated, refs)
  end

  defp resolve_borrowed(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["core", 0]},
               %{"Ident" => ["io", 0]},
               %{"Ident" => ["error", 0]},
               %{
                 "Impl" => %{
                   "Ty" => %{
                     "kind" => "InherentImplBlock",
                     "params" => parent_params,
                     "skip_binder" => parent
                   }
                 }
               },
               %{"Ident" => [method, 0]}
             ]
           },
           "generics" => params
         } <- function,
         true <- method in ["kind", "is_interrupted"],
         true <- plain?(params, 1) and plain?(parent_params, 0),
         %{"def_id" => error} <- FileModels.error_declaration(translated),
         %{"def_id" => kind} <- kind_declaration(translated),
         true <- CallModels.expand(parent, refs) == adt(error),
         true <-
           CallModels.expand(sig["inputs"], refs) == [
             %{"Ref" => [%{"Var" => %{"Free" => 0}}, adt(error), "Shared"]}
           ],
         true <-
           CallModels.expand(sig["output"], refs) ==
             if(method == "kind", do: adt(kind), else: %{"Scalar" => "Bool"}),
         true <-
           method != "is_interrupted" or
             Enum.any?(
               kind_declaration(translated)["kind"]["Enum"],
               &(&1["name"] == "Interrupted")
             ) do
      operation = if method == "kind", do: "kind", else: "isInterrupted"

      %{
        rust_name: "core::io::error::{core::io::error::Error}::#{method}",
        lean: "Lynx.NativeIoError.kind",
        builtin: false,
        can_fail: true,
        lift: true,
        native_cutoff_only: true,
        native_file_types: {nil, error},
        io_error_kind_type: kind,
        io_error_operation: operation,
        label:
          "Error::#{method} model: allocation-free simple/static values retain their kind and static message bytes; standard OS errors require a unique live callback-free capability and a separate unique bounded immutable classification descriptor naming an actual extracted ErrorKind variant; OS admission asserts that the standard is_interrupted callback agrees with the Interrupted kind; missing, stale, ambiguous, custom or unknown classification exhausts verification; std representation, host/OS callback correspondence, allocation and FFI remain unverified; custom error payloads are not included"
      }
    else
      _ -> nil
    end
  end

  defp resolve_static(function, translated, refs) do
    with %{
           "body" => "Opaque",
           "src" => "Normal",
           "signature" => %{"is_unsafe" => false, "is_variadic" => false, "abi" => "Rust"} = sig,
           "generics" => params,
           "item_meta" => %{
             "name" => [
               %{"Ident" => ["core", 0]},
               %{"Ident" => ["io", 0]},
               %{"Ident" => ["error", 0]},
               %{
                 "Impl" => %{
                   "Ty" => %{
                     "kind" => "InherentImplBlock",
                     "params" => parent_params,
                     "skip_binder" => parent
                   }
                 }
               },
               %{"Ident" => ["from_static_message", 0]}
             ]
           }
         } <- function,
         true <- plain?(params, 0) and plain?(parent_params, 0),
         %{"def_id" => error} <- FileModels.error_declaration(translated),
         %{"def_id" => kind} <- kind_declaration(translated),
         [message] <-
           Enum.filter(
             translated["type_decls"],
             &(&1 &&
                 &1["item_meta"]["name"] ==
                   Enum.map(~w(core io error SimpleMessage), fn part ->
                     %{"Ident" => [part, 0]}
                   end))
           ),
         %{
           "src" => "Normal",
           "generics" => message_params,
           "kind" => %{"Struct" => [first, second]}
         } <- message,
         true <- plain?(message_params, 0),
         true <- first["name"] == "kind" and CallModels.expand(first["ty"], refs) == adt(kind),
         true <- second["name"] == "message",
         %{
           "Ref" => [
             "Static",
             %{"Adt" => %{"builtin" => "Str", "generics" => str_args}},
             "Shared"
           ]
         } <- CallModels.expand(second["ty"], refs),
         true <- str_args == ResourceModels.args([]),
         true <- CallModels.expand(parent, refs) == adt(error),
         true <-
           CallModels.expand(sig["inputs"], refs) == [
             %{"Ref" => ["Static", adt(message["def_id"]), "Shared"]}
           ],
         true <- CallModels.expand(sig["output"], refs) == adt(error) do
      %{
        rust_name: "core::io::error::{core::io::error::Error}::from_static_message",
        lean: "Lynx.NativeIoError.fromStaticMessage",
        builtin: false,
        can_fail: true,
        lift: true,
        native_cutoff_only: true,
        native_file_types: {nil, error},
        io_error_kind_type: kind,
        io_error_message_type: message["def_id"],
        io_error_operation: "fromStaticMessage",
        label:
          "Standard Error::from_static_message model: retain the actual extracted SimpleMessage kind and message bytes in a disjoint allocation-free value; classification and destruction do not consume an OS error capability; native bitpacked/static pointer layout, std representation and FFI correspondence unverified; custom payloads unsupported"
      }
    else
      _ -> nil
    end
  end

  def scope(audit, prefix) do
    calls =
      Map.new(audit.external_calls, fn {id, model} ->
        if model[:io_error_kind_type],
          do: {id, %{model | lean: prefix <> ".IoErrorModel." <> model.io_error_operation}},
          else: {id, model}
      end)

    %{audit | external_calls: calls}
  end

  def install!(audit, translation, output, prefix) do
    case audit.external_calls
         |> Map.values()
         |> Enum.map(& &1[:io_error_kind_type])
         |> Enum.reject(&is_nil/1)
         |> Enum.uniq() do
      [] ->
        []

      [id] ->
        declaration = kind_declaration(audit.translated)

        unless declaration && declaration["def_id"] == id,
          do: raise(ArgumentError, "I/O error kind declaration correspondence mismatch")

        [type] = Enum.filter(translation["types"], &(&1["def_id"] == id))

        unless type["rust_name"] == Enum.join(@kind, "::"),
          do: raise(ArgumentError, "I/O error kind translation correspondence mismatch")

        module = prefix <> ".IoErrorModel"
        path = Path.join(output, String.replace(module, ".", "/") <> ".lean")

        case File.read(path) do
          {:ok, "-- Generated by Lynx:" <> _} -> :ok
          {:error, :enoent} -> :ok
          _ -> raise ArgumentError, "refusing to overwrite a user Lean module: #{path}"
        end

        cases =
          Enum.map_join(declaration["kind"]["Enum"], "\n", fn variant ->
            "    | #{JSON.encode!(variant["name"])} => .ok .#{variant["name"]}"
          end)

        labels =
          Enum.map_join(declaration["kind"]["Enum"], "\n", fn variant ->
            "    | .#{variant["name"]} => #{JSON.encode!(variant["name"])}"
          end)

        interrupted =
          if Enum.any?(audit.external_calls, fn {_, m} ->
               m[:io_error_operation] == "isInterrupted"
             end) do
            """
            @[expose] def isInterrupted (error : Lynx.NativeIoError) : Lynx.NativeM Bool := do
              let value ← kind error
              .ok (match value with | .Interrupted => true | _ => false)
            """
          else
            ""
          end

        factory =
          case Enum.uniq(
                 for {_, m} <- audit.external_calls,
                     m[:io_error_message_type],
                     do: m.io_error_message_type
               ) do
            [] ->
              ""

            [message] ->
              [message_type] = Enum.filter(translation["types"], &(&1["def_id"] == message))

              unless message_type["rust_name"] == "core::io::error::SimpleMessage",
                do: raise(ArgumentError, "I/O static message translation correspondence mismatch")

              """
              @[expose] def fromStaticMessage (message : #{message_type["lean_name"]}) : Lynx.NativeM Lynx.NativeIoError :=
                .ok (.staticMessage (encodeKind message.kind) (Lynx.NativeFile.bytes message.message))
              """
          end

        File.mkdir_p!(Path.dirname(path))

        File.write!(path, """
        -- Generated by Lynx: checked standard ErrorKind conversion.
        module
        public import #{prefix}.Types
        public section
        namespace #{module}
        @[expose] def encodeKind (kind : #{type["lean_name"]}) : String :=
          match kind with
        #{labels}
        @[expose] def decodeKind (label : String) : Except Lynx.Exception #{type["lean_name"]} :=
          match label with
        #{cases}
            | _ => .error .exhausted
        @[expose] def kind (error : Lynx.NativeIoError) : Lynx.NativeM #{type["lean_name"]} := do
          let label ← Lynx.NativeIoError.kind error
          Lynx.Result.ofExcept (decodeKind label)
        #{interrupted}
        #{factory}
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

  defp kind_declaration(translated) do
    case Enum.filter(
           translated["type_decls"],
           &(&1 &&
               &1["item_meta"]["name"] ==
                 Enum.map(@kind, fn part -> %{"Ident" => [part, 0]} end))
         ) do
      [%{"src" => "Normal", "generics" => params, "kind" => %{"Enum" => variants}} = type]
      when is_list(variants) and variants != [] ->
        if plain?(params, 0) and
             Enum.all?(
               variants,
               &(&1["fields"] == [] and is_binary(&1["name"]) and
                   Regex.match?(~r/\A[A-Z][A-Za-z0-9_]*\z/, &1["name"]))
             ) and
             length(Enum.uniq_by(variants, & &1["name"])) == length(variants),
           do: type

      _ ->
        nil
    end
  end

  defp adt(id),
    do: %{"Adt" => %{"id" => id, "builtin" => nil, "generics" => ResourceModels.args([])}}

  defp plain?(params, regions) when is_map(params) do
    is_list(params["regions"]) and length(params["regions"]) == regions and
      Enum.all?(Enum.with_index(params["regions"]), fn {region, index} ->
        region["index"] == index
      end) and
      Enum.all?(
        ~w(types const_generics trait_clauses outlives trait_type_constraints),
        &(params[&1] == [])
      )
  end

  defp plain?(_, _), do: false
end
