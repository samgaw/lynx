defmodule Lynx.Rustler.Adapter do
  @moduledoc false

  # Bind the actual extracted computation to a shared decoding/execution/encoding
  # model. No result or user contract replaces an implementation definition.
  def external!(manifest, implementations, opts \\ []) do
    beam_module = String.to_atom(manifest.module)
    module = :lynx_core_to_leanj.module_name(beam_module)
    implementation = Keyword.fetch!(opts, :implementation_module)
    module_name = identifier!(module)

    modules =
      implementations |> Map.values() |> Enum.map(&lean_module!(&1["lean_file"])) |> Enum.uniq()

    bridge = Keyword.fetch!(opts, :bridge_module)

    proof_modules = Keyword.get(opts, :proof_modules, [])

    imported =
      Enum.map_join(
        Enum.uniq([bridge | modules ++ proof_modules]),
        "\n",
        &("public import " <> identifier!(&1))
      )

    execution = Keyword.get(opts, :execution, :pure)

    unless execution in [:pure, :runtime],
      do: raise(ArgumentError, "unsupported Rust execution model: #{inspect(execution)}")

    resources = Keyword.get(opts, :resource_types, [])

    if resources != [] and execution != :runtime,
      do: raise(ArgumentError, "resource registration requires runtime execution")

    owned = Keyword.get(opts, :owned_drops, false)

    unless is_boolean(owned) and (not owned or execution == :runtime),
      do:
        raise(
          ArgumentError,
          "owned resource cleanup requires runtime execution and a boolean owned_drops option"
        )

    release = if owned, do: "Lynx.NativeOwnedDrop.drop", else: "Lynx.NativeResourceArc.release"

    declarations =
      Enum.map_join(manifest.bindings, "\n", &declaration!(&1, execution, resources, release))

    source = """
    module
    public import Lynx.Rustler
    #{imported}
    open Aeneas Aeneas.Std
    public section
    namespace #{module_name}
    #{declarations}
    end #{module_name}
    """

    file_name = implementation <> ".lean"

    file = %{
      "module" => implementation,
      "file" => file_name,
      "imports" => [],
      "contents" => [],
      "audit_modules" => [
        implementation,
        bridge | modules ++ proof_modules ++ Keyword.get(opts, :audit_modules, [])
      ],
      "preludes" => [
        %{"source" => source, "file" => file_name, "span" => [1], "indentation" => 0}
      ]
    }

    bindings =
      for binding <- manifest.bindings,
          do: {beam_module, String.to_atom(binding["name"]), binding["arity"]}

    %Lynx.External{
      bindings: bindings,
      purities: if(execution == :runtime, do: Map.new(bindings, &{&1, :concurrent}), else: %{}),
      files: [file],
      fingerprint: opts[:fingerprint],
      implementation_modules: %{beam_module => implementation},
      native_exports: %{
        beam_module =>
          Enum.map(manifest.exports, fn {name, arity, _flags} -> {String.to_atom(name), arity} end)
      }
    }
  end

  defp declaration!(binding, execution_model, resources, release) do
    result = type!(binding["result"])
    args = for index <- indices(binding["arity"]), do: "arg#{index}"
    decoded = Enum.map(args, &("decoded_" <> &1))
    types = Enum.map(binding["arguments"], &type!/1)

    if Enum.any?(types, &is_nil(&1.decode)),
      do: raise(ArgumentError, "custom Rustler decoders are unsupported")

    if execution_model != :runtime and
         (result[:resource] == true or Enum.any?(types, & &1[:resource])),
       do: raise(ArgumentError, "resource NIF codecs require runtime execution")

    runtime? = execution_model == :runtime
    monad = if runtime?, do: "Lynx.NativeM", else: "RustM"

    return_type =
      if runtime?, do: "Lynx.Result Lynx.Term", else: "Except Lynx.Exception Lynx.Term"

    dispatcher = if runtime?, do: "(_dispatcher : Lynx.Dispatcher)", else: ""

    params =
      Enum.zip_with(args, types, fn arg, type -> "(#{arg} : #{type.lean})" end) |> Enum.join(" ")

    term_params = Enum.map_join(args, " ", &("(" <> &1 <> " : Lynx.Term)"))
    native = identifier!(binding["lean_name"])
    call = Enum.join([native | args], " ")

    execution =
      atomic_identifier!(binding["name"] <> ":execution/" <> Integer.to_string(binding["arity"]))

    wrapper = atomic_identifier!(binding["name"] <> "/" <> Integer.to_string(binding["arity"]))

    decode =
      Enum.with_index(Enum.zip([args, decoded, types]))
      |> Enum.map_join("\n", fn {{arg, value, type}, index} ->
        decoder = "#{type.decode} #{arg}"

        decoder =
          if runtime? and !type[:resource], do: "Lynx.Result.ofExcept (#{decoder})", else: decoder

        owned =
          Enum.zip(decoded, types)
          |> Enum.take(index)
          |> Enum.filter(fn {_, t} -> t[:resource] end)
          |> Enum.reverse()

        decoder =
          if owned == [] do
            decoder
          else
            cleanup =
              Enum.map_join(owned, "; ", fn {name, _} ->
                "#{release} #{name}"
              end)

            "Lynx.Result.handle (#{decoder}) (fun error => do #{cleanup}; Lynx.Result.error error)"
          end

        "  let #{value} ← #{decoder}"
      end)

    invocation = Enum.join([execution | decoded], " ")
    direct = Enum.join([native | decoded], " ")

    adapter_theorem =
      atomic_identifier!(binding["name"] <> ":adapter/" <> Integer.to_string(binding["arity"]))

    wrapper_call =
      Enum.join([wrapper | if(runtime?, do: ["_dispatcher" | args], else: args)], " ")

    body = "do\n#{decode}\n  #{execute(invocation, result, execution_model, release)}"
    direct_body = "do\n#{decode}\n  #{execute(direct, result, execution_model, release)}"

    registry =
      if resources == [], do: "", else: "Lynx.Rustler.withResourceTypes #{lean_list(resources)} "

    """
    @[expose] def #{execution} #{params} : #{monad} #{result.lean} := #{call}

    @[expose] def #{wrapper} #{dispatcher} #{term_params} : #{return_type} := #{registry}(#{body})

    theorem #{adapter_theorem} #{dispatcher} #{term_params} :
        #{wrapper_call} = #{registry}(#{direct_body}) := rfl
    """
  end

  defp lean_list(strings), do: "[" <> Enum.map_join(strings, ", ", &JSON.encode!/1) <> "]"

  defp execute(call, %{resource: true}, :runtime, release) do
    "Lynx.Rustler.executeNative (do let value ← (#{call}); let term ← Lynx.NativeResourceArc.encode value; #{release} value; Lynx.Result.ok term) id"
  end

  defp execute(call, %{encode_m: encoder}, :runtime, _release) do
    "Lynx.Rustler.executeNative (do let value ← (#{call}); Lynx.NativeM.fromRust (#{encoder} value)) id"
  end

  defp execute(call, type, :runtime, _release),
    do: "Lynx.Rustler.executeNative (#{call}) #{type.encode}"

  defp execute(call, %{encode_m: encoder}, :pure, _release) do
    "Lynx.Rustler.execute (do let value ← (#{call}); #{encoder} value) id"
  end

  defp execute(call, type, :pure, _release), do: "Lynx.Rustler.execute (#{call}) #{type.encode}"

  defp monadic_encoder(%{encode_m: encoder}), do: encoder
  defp monadic_encoder(type), do: "(fun value => RustM.ok (#{type.encode} value))"

  defp type!(%{"resource" => _, "lean" => lean}) do
    payload = identifier!(lean)

    %{
      lean: "(Lynx.NativeResourceArc #{payload})",
      resource: true,
      decode: "Lynx.NativeResourceArc.decode (α := #{payload})",
      encode: nil
    }
  end

  defp type!(%{"native" => _, "lean" => lean, "encoder" => encoder}) do
    type = identifier!(lean)

    %{
      lean: type,
      decode: nil,
      encode: nil,
      encode_m: "(fun (value : #{type}) => #{identifier!(encoder)} value ())"
    }
  end

  defp type!("bool"),
    do: %{lean: "Bool", decode: "Lynx.Rustler.decodeBool", encode: "Lynx.Rustler.encodeBool"}

  defp type!("binary"),
    do: %{
      lean: "Lynx.Rustler.Binary",
      decode: "Lynx.Rustler.decodeBinary",
      encode: "Lynx.Rustler.encodeBinary"
    }

  defp type!(%{"vec" => "u8"}),
    do: %{
      lean: "(alloc.vec.Vec U8)",
      decode: "Lynx.Rustler.decodeByteVec",
      encode: nil,
      encode_m: "Lynx.Rustler.encodeByteVec"
    }

  defp type!(<<sign, width::binary>> = type)
       when sign in [?i, ?u] and width in ["8", "16", "32", "64"] do
    signed = sign == ?i
    family = if signed, do: "Signed", else: "Unsigned"
    decoder_bits = if width in ["8", "16"], do: "32", else: width
    name = String.upcase(type)

    %{
      lean: name,
      decode: "Lynx.Rustler.decode#{family} .#{name} #{decoder_bits}",
      encode: "Lynx.Rustler.encode#{family}"
    }
  end

  defp type!(%{"tuple" => fields}) when is_list(fields) and length(fields) <= 7 do
    types = Enum.map(fields, &type!/1)

    if Enum.any?(types, & &1[:resource]),
      do:
        raise(ArgumentError, "resource codecs currently require top-level NIF arguments/results")

    lean =
      case types do
        [] -> "Unit"
        [type] -> type.lean
        _ -> "(" <> Enum.map_join(types, " × ", & &1.lean) <> ")"
      end

    names = Enum.map(indices(length(types)), &"field#{&1}")

    tuple =
      case names do
        [] -> "()"
        [name] -> name
        _ -> "(" <> Enum.join(names, ", ") <> ")"
      end

    decodings =
      Enum.zip(types, names)
      |> Enum.with_index()
      |> Enum.flat_map(fn {{type, name}, index} ->
        [
          "let raw_#{name} ← Lynx.Rustler.tupleField fields #{index}",
          "let #{name} ← #{type.decode} raw_#{name}"
        ]
      end)

    encoded =
      types
      |> Enum.with_index()
      |> Enum.map_join(", ", fn {type, index} ->
        projection =
          cond do
            length(types) == 1 -> "value"
            index == length(types) - 1 -> "value" <> String.duplicate(".2", index)
            true -> "value" <> String.duplicate(".2", index) <> ".1"
          end

        "#{type.encode} (#{projection})"
      end)

    fields_var = if types == [], do: "_fields", else: "fields"
    value_var = if types == [], do: "_value", else: "value"

    statements =
      ["let #{fields_var} ← Lynx.Rustler.decodeTuple #{length(types)} input"] ++
        decodings ++ ["pure #{tuple}"]

    type = %{
      lean: lean,
      decode:
        if(Enum.any?(types, &is_nil(&1.decode)),
          do: nil,
          else: "(fun (input : Lynx.Term) => do #{Enum.join(statements, "; ")})"
        ),
      encode: "(fun (#{value_var} : #{lean}) => Lynx.Term.tuple #[#{encoded}])"
    }

    if Enum.any?(types, &Map.has_key?(&1, :encode_m)) do
      values = for index <- indices(length(types)), do: "encoded#{index}"

      steps =
        Enum.zip(types, values)
        |> Enum.with_index()
        |> Enum.map(fn {{type, name}, index} ->
          projection =
            cond do
              length(types) == 1 -> "value"
              index == length(types) - 1 -> "value" <> String.duplicate(".2", index)
              true -> "value" <> String.duplicate(".2", index) <> ".1"
            end

          "let #{name} ← #{monadic_encoder(type)} (#{projection})"
        end)

      Map.merge(type, %{
        encode: nil,
        encode_m:
          "(fun (value : #{lean}) => do " <>
            Enum.join(steps ++ [".ok (Lynx.Term.tuple #[#{Enum.join(values, ", ")}])"], "; ") <>
            ")"
      })
    else
      type
    end
  end

  defp type!(%{"option" => inner}) do
    inner = type!(inner)

    if inner[:resource],
      do:
        raise(ArgumentError, "resource codecs currently require top-level NIF arguments/results")

    type = %{
      lean: "(Option #{inner.lean})",
      decode:
        if(is_nil(inner.decode),
          do: nil,
          else: "Lynx.Rustler.decodeOption (#{inner.decode})"
        ),
      encode: "(Lynx.Rustler.encodeOption (#{inner.encode}))"
    }

    if Map.has_key?(inner, :encode_m),
      do:
        Map.merge(type, %{
          encode: nil,
          encode_m: "(Lynx.Rustler.encodeOptionM (#{monadic_encoder(inner)}))"
        }),
      else: type
  end

  defp type!(%{"result" => [ok, err]}) do
    ok = type!(ok)
    err = type!(err)

    if ok[:resource] == true or err[:resource] == true,
      do:
        raise(ArgumentError, "resource codecs currently require top-level NIF arguments/results")

    type = %{
      lean: "(core.result.Result #{ok.lean} #{err.lean})",
      decode:
        if(is_nil(ok.decode) or is_nil(err.decode),
          do: nil,
          else: "Lynx.Rustler.decodeResult (#{ok.decode}) (#{err.decode})"
        ),
      encode: "(Lynx.Rustler.encodeResult (#{ok.encode}) (#{err.encode}))"
    }

    if Map.has_key?(ok, :encode_m) or Map.has_key?(err, :encode_m),
      do:
        Map.merge(type, %{
          encode: nil,
          encode_m:
            "(Lynx.Rustler.encodeResultM (#{monadic_encoder(ok)}) (#{monadic_encoder(err)}))"
        }),
      else: type
  end

  defp type!(type), do: raise(ArgumentError, "unsupported Rustler adapter type: #{inspect(type)}")

  defp indices(0), do: []
  defp indices(arity), do: Enum.to_list(1..arity)

  defp identifier!(name) do
    name |> String.split(".") |> Enum.map_join(".", &atomic_identifier!/1)
  end

  defp atomic_identifier!(name) do
    if String.contains?(name, ["«", "»", "\n", "\r"]),
      do: raise(ArgumentError, "unsupported Lean identifier in native binding")

    "«" <> name <> "»"
  end

  defp lean_module!(file) do
    if Path.type(file) != :relative || ".." in Path.split(file) || Path.extname(file) != ".lean",
      do: raise(ArgumentError, "invalid Aeneas module path: #{inspect(file)}")

    file |> Path.rootname() |> String.replace("/", ".")
  end
end
