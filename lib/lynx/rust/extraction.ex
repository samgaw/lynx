defmodule Lynx.Rust.Extraction do
  @moduledoc false

  # Extraction is independent of Rustler. This result is not a proof report;
  # clients must kernel-check their properties and audit the generated modules.
  def run!(context, tools, roots, output, module, opts \\ []) do
    for key <- Keyword.keys(opts),
        key not in [:external_types, :external_calls],
        do: raise(ArgumentError, "unknown Rust extraction option: #{key}")

    %{document: document, llbc: llbc, first_party: first_party, models: models} =
      describe!(context, tools, roots, output, module, Keyword.take(opts, [:external_types]))

    tools = Path.expand(tools)
    output = Path.expand(output)
    requested_calls = Keyword.get(opts, :external_calls, [])

    if :rustler_binary_as_slice in requested_calls and
         not Enum.any?(
           models,
           &(&1.rust == "rustler::types::binary::Binary" and &1.lean == "Lynx.Rustler.Binary")
         ),
       do: raise(ArgumentError, "Rustler as_slice requires the explicit Binary FFI type model")

    audit = Lynx.Rust.LLBC.audit!(document, first_party, external_calls: requested_calls)
    audit = Map.put(audit, :external_types, models)

    model_args =
      if models == [] and map_size(audit.external_calls) == 0 do
        []
      else
        path = Path.join(output, String.replace(module, ".", "_") <> ".external-types.json")

        File.write!(
          path,
          JSON.encode!(%{
            "types" =>
              Enum.map(
                models,
                &%{
                  "rust_pattern" => &1.rust,
                  "extract_name" => &1.lean
                }
              ),
            "functions" =>
              Enum.map(
                Enum.reject(Map.values(audit.external_calls), & &1.builtin),
                &%{
                  "rust_pattern" => &1.rust_name,
                  "extract_name" => &1.lean,
                  "can_fail" => &1.can_fail,
                  "lift" => &1.lift
                }
              )
          })
        )

        ["-external-names", path] ++
          if(models == [],
            do: [],
            else: ["-extra-includes", Enum.map_join(models, ",", & &1.import)]
          )
      end

    run!(
      Path.join(tools, "aeneas"),
      model_args ++
        [
          "-backend",
          "lean",
          "-split-files",
          "-emit-json",
          "-abort-on-error",
          "-warnings-as-errors",
          "-dest",
          output,
          "-subdir",
          String.replace(module, ".", "/"),
          llbc
        ]
    )

    translation_bytes = File.read!(Path.join(output, "translation.json"))
    translation = JSON.decode!(translation_bytes)
    implementations = Lynx.Rust.LLBC.link!(audit, translation)
    # Keep per-root metadata, since several extractions can share one Lean package.
    File.write!(
      Path.join(output, String.replace(module, ".", "_") <> ".translation.json"),
      translation_bytes
    )

    %{
      audit: audit,
      translation: translation,
      implementations: implementations,
      constants: Lynx.Rust.Constants.link!(audit.constants, translation),
      external_types: models,
      fingerprint:
        Lynx.Rust.Fingerprint.extraction!(context, tools, llbc, translation_bytes, first_party)
        |> then(fn digest ->
          if models == [] and requested_calls == [] and map_size(audit.external_calls) == 0,
            do: digest,
            else:
              Lynx.Rust.Fingerprint.digest(
                :erlang.term_to_binary(
                  {digest, models, requested_calls,
                   audit.external_calls
                   |> Map.values()
                   |> Enum.map(&Map.drop(&1, [:function, :definition_id]))
                   |> Enum.sort()},
                  [:deterministic]
                )
              )
        end),
      llbc: llbc,
      output: output,
      module: module
    }
  end

  # This stage discovers resolved Rust identities, including unsupported code.
  # It makes no verification claim. run!/6 always applies the full audit before
  # invoking Aeneas or producing an implementation/proof linkage.
  @doc false
  def describe!(context, tools, roots, output, module, opts \\ []) do
    for key <- Keyword.keys(opts),
        key != :external_types,
        do: raise(ArgumentError, "unknown Rust discovery option: #{key}")

    unless roots != [] && Enum.all?(roots, &is_binary/1),
      do: raise(ArgumentError, "Rust extraction requires explicit function roots")

    unless Regex.match?(~r/^[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*$/, module),
      do: raise(ArgumentError, "invalid generated Lean module prefix: #{inspect(module)}")

    tools = Path.expand(tools)
    output = Path.expand(output)
    File.mkdir_p!(output)
    charon = Path.join(tools, "charon")
    {toolchain, 0} = System.cmd(charon, ["toolchain-version"], stderr_to_stdout: true)

    unless String.trim(toolchain) == context.toolchain,
      do: raise("Charon toolchain does not match the Cargo compilation")

    first_party = Lynx.Rust.LLBC.crate_names!(context.workspace)
    models = Keyword.get(opts, :external_types, [])

    for model <- models do
      unless is_binary(model.rust) and
               Regex.match?(~r/^[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)+$/, model.rust) and
               hd(String.split(model.rust, "::")) not in first_party and
               is_binary(model.lean) and is_binary(model.label) and
               Regex.match?(~r/^[A-Z][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$/, model.lean) and
               Regex.match?(~r/^[A-Z][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$/, model.import),
             do:
               raise(
                 ArgumentError,
                 "invalid external Rust type model or first-party type replacement"
               )
    end

    unless length(models) == MapSet.size(MapSet.new(models, & &1.rust)),
      do: raise(ArgumentError, "duplicate external Rust type model")

    root_args = Enum.flat_map(roots, &["--start-from", &1])
    includes = Enum.flat_map(first_party, &["--include", &1])
    llbc = Path.join(output, String.replace(module, ".", "_") <> ".llbc")

    args =
      [
        "rustc",
        "--sysroot",
        "default",
        "--preset=aeneas",
        "--opaque",
        "core",
        "--opaque",
        "alloc",
        "--opaque",
        "std",
        "--include",
        "core::result::Result",
        "--include",
        "core::option::Option",
        "--include",
        "core::ops::control_flow::ControlFlow",
        "--include",
        "core::fmt::Error",
        "--dest-file",
        llbc
      ] ++
        root_args ++
        includes ++
        Enum.flat_map(Lynx.Rust.LibraryHelpers.includes(), &["--include", &1]) ++
        Enum.flat_map(models, &["--opaque", &1.rust]) ++
        ["--"] ++ Lynx.Rust.Cargo.extraction_arguments(context, output)

    diagnostics =
      run!(charon, args,
        cd: context.record["directory"],
        env: Lynx.Rust.Cargo.environment(context)
      )

    document = read_llbc!(llbc, diagnostics)
    validate_target!(document)

    %{document: document, llbc: llbc, first_party: first_party, models: models}
  end

  @doc false
  def read_llbc!(path, diagnostics) do
    document = JSON.decode!(File.read!(path))

    if document["has_errors"] == true,
      do:
        raise(
          ArgumentError,
          "Charon reported extraction errors for #{path}:\n#{diagnostics}"
        )

    document
  end

  # The pinned Aeneas usize/isize models use Lean's host pointer width. Reject
  # extraction targets that cannot agree with those models rather than silently
  # proving a different machine's arithmetic.
  def validate_target!(document) do
    expected_bytes = :erlang.system_info(:wordsize)

    case document["translated"]["target_information"] do
      [%{"value" => %{"target_pointer_size" => ^expected_bytes, "is_little_endian" => true}}] ->
        :ok

      targets ->
        raise ArgumentError,
              "unsupported Rust target for the Lean runtime: expected one little-endian #{expected_bytes * 8}-bit target, got #{inspect(targets)}"
    end
  end

  defp run!(executable, args, opts \\ []) do
    {output, status} = System.cmd(executable, args, Keyword.put(opts, :stderr_to_stdout, true))
    if status != 0, do: raise("Rust extraction failed in #{executable} (#{status}):\n#{output}")
    output
  end
end
