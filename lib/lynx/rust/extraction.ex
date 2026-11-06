defmodule Lynx.Rust.Extraction do
  @moduledoc false

  # Extraction is independent of Rustler. This result is not a proof report;
  # clients must kernel-check their properties and audit the generated modules.
  def run!(context, tools, roots, output, module, opts \\ []) do
    for key <- Keyword.keys(opts),
        key not in [:external_types, :external_calls, :rustler_atoms, :execution, :unwind],
        do: raise(ArgumentError, "unknown Rust extraction option: #{key}")

    unwind = Keyword.get(opts, :unwind, :reject)
    Lynx.Rust.NativeUnwind.charon_arguments(unwind)

    if unwind != :reject and Keyword.get(opts, :execution, :pure) != :runtime,
      do: raise(ArgumentError, "assertion unwind requires runtime execution")

    if :rustler_encoders in Keyword.get(opts, :external_calls, []),
      do: Lynx.Rustler.require_rustler!(context)

    discovery =
      describe!(
        context,
        tools,
        roots,
        output,
        module,
        Keyword.take(opts, [:external_types, :unwind])
      )

    {discovery, caches} =
      case Keyword.get(opts, :rustler_atoms, []) do
        [] ->
          {discovery, []}

        modules ->
          modules =
            if modules == :discover,
              do: Lynx.Rustler.AtomCaches.modules(discovery.document),
              else: modules

          expanded =
            Path.join(Path.expand(output), String.replace(module, ".", "_") <> ".atoms.rs")

          File.write!(expanded, Lynx.Rust.Cargo.expand!(context))
          metadata = Lynx.Rustler.Metadata.atom_caches!(expanded, modules)
          caches = Lynx.Rustler.AtomCaches.resolve!(discovery.document, metadata)

          unless length(caches) == length(Enum.uniq(modules)),
            do: raise(ArgumentError, "missing selected Rustler atom cache")

          opaque = Enum.map(caches, & &1.opaque_pattern)

          {describe!(
             context,
             tools,
             roots,
             output,
             module,
             Keyword.take(opts, [:external_types, :unwind]),
             opaque
           ), caches}
      end

    discovery =
      if Keyword.get(opts, :execution, :pure) == :runtime and
           Lynx.Rust.NativeDrops.needs_lowering?(discovery.document) do
        describe!(
          context,
          tools,
          Enum.uniq(roots ++ ["core::mem::drop"]),
          output,
          module,
          Keyword.take(opts, [:external_types, :unwind]),
          Enum.map(caches, & &1.opaque_pattern)
        )
      else
        discovery
      end

    %{document: document, llbc: llbc, first_party: first_party, models: models} = discovery

    {document, nonpanicking_borrows} =
      if Keyword.get(opts, :execution, :pure) == :runtime,
        do: Lynx.Rust.NativeBorrows.prune_owned_calls!(document, first_party),
        else: {document, []}

    {document, native_unwind} =
      if unwind == :assertions,
        do: Lynx.Rust.NativeUnwind.lower!(document, first_party),
        else: {document, []}

    {document, native_drops} =
      if Keyword.get(opts, :execution, :pure) == :runtime,
        do: Lynx.Rust.NativeDropLowering.lower!(document, first_party),
        else: {document, []}

    {document, nonpanicking} =
      if Keyword.get(opts, :execution, :pure) == :runtime,
        do: Lynx.Rust.NativeUnwind.nonpanicking_drops!(document),
        else: {document, []}

    native_unwind = nonpanicking_borrows ++ native_unwind ++ nonpanicking

    document =
      if native_drops != [] or native_unwind != [],
        do: Lynx.Rust.LLBCJson.restore_spans!(document, discovery.document),
        else: document

    backend_llbc =
      if native_drops == [] and native_unwind == [] do
        llbc
      else
        path = Path.rootname(llbc) <> ".native-drops.llbc"
        File.write!(path, Lynx.Rust.LLBCJson.encode_like!(document, llbc))
        path
      end

    cache_models = Lynx.Rustler.AtomCaches.models!(document, caches, module)

    if caches != [] and
         not Enum.any?(
           models,
           &(&1.rust == "rustler::types::atom::Atom" and
               &1.lean == "Lynx.Rustler.Atom")
         ),
       do: raise(ArgumentError, "Rustler atom caches require the explicit Atom FFI type model")

    tools = Path.expand(tools)
    output = Path.expand(output)
    requested_calls = Keyword.get(opts, :external_calls, [])

    if :rustler_encoders in requested_calls do
      for {rust, lean} <- [
            {"rustler::env::Env", "Lynx.Rustler.Env"},
            {"rustler::term::Term", "Lynx.Rustler.NativeTerm"},
            {"rustler::types::atom::Atom", "Lynx.Rustler.Atom"}
          ],
          not Enum.any?(models, &(&1.rust == rust and &1.lean == lean)),
          do: raise(ArgumentError, "Rustler Encoder requires the explicit #{rust} FFI type model")
    end

    if :rustler_binary_as_slice in requested_calls and
         not Enum.any?(
           models,
           &(&1.rust == "rustler::types::binary::Binary" and &1.lean == "Lynx.Rustler.Binary")
         ),
       do: raise(ArgumentError, "Rustler as_slice requires the explicit Binary FFI type model")

    audit =
      Lynx.Rust.LLBC.audit!(document, first_party,
        external_calls: requested_calls,
        unwind: unwind,
        execution: Keyword.get(opts, :execution, :pure),
        rustler_atom_caches: {caches, module}
      )

    models =
      models ++
        Lynx.Rust.MutexModels.type_models(audit.external_calls, module) ++
        Lynx.Rust.LockModels.type_models(audit.external_calls, module)

    unless length(models) == MapSet.size(MapSet.new(models, & &1.rust)),
      do: raise(ArgumentError, "conflicting native Rust type models")

    audit = Map.put(audit, :external_types, models)
    audit = Lynx.Rust.BytesModels.scope(audit, module)
    codec_plan = Lynx.Rust.NativeCodecs.plan!(audit)

    {backend_document, compiler_drop_queries} = Lynx.Rust.LLBCJson.drop_query_metadata!(document)

    backend_llbc =
      if compiler_drop_queries == [] do
        backend_llbc
      else
        path = Path.rootname(llbc) <> ".aeneas.llbc"
        File.write!(path, Lynx.Rust.LLBCJson.encode_like!(backend_document, llbc))
        path
      end

    model_args =
      if models == [] and map_size(audit.external_calls) == 0 do
        []
      else
        path = Path.join(output, String.replace(module, ".", "_") <> ".external-types.json")

        File.write!(
          path,
          JSON.encode!(
            Map.merge(
              %{
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
                    &Map.merge(
                      %{
                        "rust_pattern" => &1.rust_name,
                        "extract_name" => &1.lean,
                        "can_fail" => &1.can_fail,
                        "lift" => &1.lift
                      },
                      if(Map.has_key?(&1, :keep_params),
                        do: %{"keep_params" => &1.keep_params},
                        else: %{}
                      )
                    )
                  )
              },
              Lynx.Rustler.EncoderModels.external_names(audit.external_calls)
            )
          )
        )

        ["-external-names", path] ++
          if(models == [],
            do: [],
            else: ["-extra-includes", Enum.map_join(models, ",", & &1.import)]
          )
      end

    execution = Keyword.get(opts, :execution, :pure)

    {result_monad, runtime_args, runtime_modules} =
      Lynx.Rust.Runtime.configuration!(execution, output, module)

    run!(
      Path.join(tools, "aeneas"),
      runtime_args ++
        Lynx.Rust.NativeUnwind.backend_arguments!(unwind, tools) ++
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
          backend_llbc
        ]
    )

    translation_bytes = File.read!(Path.join(output, "translation.json"))
    translation = JSON.decode!(translation_bytes)

    implementations =
      Lynx.Rust.LLBC.link!(audit, translation,
        result_monad: result_monad,
        assertion_unwind_input: unwind == :assertions
      )

    Lynx.Rustler.AtomCaches.install!(cache_models, translation, output, module)
    Lynx.Rust.BytesModels.install!(audit, translation, output, module)
    codec_modules = Lynx.Rust.NativeCodecs.install!(codec_plan, translation, output, module)

    codec_hashes =
      Enum.map(codec_modules, fn name ->
        {name,
         Lynx.Rust.Fingerprint.file!(Path.join(output, String.replace(name, ".", "/") <> ".lean"))}
      end)

    # Keep per-root metadata, since several extractions can share one Lean package.
    File.write!(
      Path.join(output, String.replace(module, ".", "_") <> ".translation.json"),
      translation_bytes
    )

    %{
      audit: audit,
      compiler_drop_queries: compiler_drop_queries,
      native_drops: native_drops,
      native_unwind: native_unwind,
      unwind: unwind,
      execution: execution,
      translation: translation,
      implementations: implementations,
      constants: Lynx.Rust.Constants.link!(audit.constants, translation),
      external_types: models,
      fingerprint:
        Lynx.Rust.Fingerprint.extraction!(context, tools, llbc, translation_bytes, first_party)
        |> then(fn digest ->
          if execution == :pure and models == [] and requested_calls == [] and
               map_size(audit.external_calls) == 0,
             do: digest,
             else:
               Lynx.Rust.Fingerprint.digest(
                 :erlang.term_to_binary(
                   {digest, Lynx.Rust.Runtime.fingerprint(execution), codec_hashes, native_drops,
                    Lynx.Rust.Fingerprint.file!(backend_llbc), unwind, native_unwind, models,
                    requested_calls,
                    audit.external_calls
                    |> Map.values()
                    |> Enum.map(&Map.drop(&1, [:function, :definition_id]))
                    |> Enum.sort()},
                   [:deterministic]
                 )
               )
        end),
      llbc: llbc,
      backend_llbc: backend_llbc,
      output: output,
      module: module,
      model_modules:
        runtime_modules ++ codec_modules ++ Lynx.Rust.BytesModels.modules(audit, module)
    }
  end

  # This stage discovers resolved Rust identities, including unsupported code.
  # It makes no verification claim. run!/6 always applies the full audit before
  # invoking Aeneas or producing an implementation/proof linkage.
  @doc false
  def describe!(context, tools, roots, output, module, opts \\ []) do
    for key <- Keyword.keys(opts),
        key not in [:external_types, :unwind],
        do: raise(ArgumentError, "unknown Rust discovery option: #{key}")

    describe!(context, tools, roots, output, module, opts, [])
  end

  defp describe!(context, tools, roots, output, module, opts, opaque) do
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
      ["rustc", "--sysroot", "default"] ++
        Lynx.Rust.NativeUnwind.charon_arguments(Keyword.get(opts, :unwind, :reject)) ++
        [
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
          "--include",
          "core::str::error::Utf8Error",
          "--dest-file",
          llbc
        ] ++
        root_args ++
        includes ++
        Enum.flat_map(Lynx.Rust.LibraryHelpers.includes(), &["--include", &1]) ++
        Enum.flat_map(models, &["--opaque", &1.rust]) ++
        Enum.flat_map(opaque, &["--opaque", &1]) ++
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
