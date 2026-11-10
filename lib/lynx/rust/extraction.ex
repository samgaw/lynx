defmodule Lynx.Rust.Extraction do
  @moduledoc false

  # Extraction is independent of Rustler. This result is not a proof report;
  # clients must kernel-check their properties and audit the generated modules.
  def run!(context, tools, roots, output, module, opts \\ []) do
    Lynx.Rust.Mir.validate!(opts)

    if :captured_unwind_drops in Keyword.get(opts, :external_calls, []),
      do:
        raise(
          ArgumentError,
          "captured unwind destruction is compiler-managed, not a user-selected external model"
        )

    for key <- Keyword.keys(opts),
        key not in [
          :external_types,
          :root_attribute,
          :mir,
          :external_calls,
          :rustler_atoms,
          :execution,
          :unwind,
          :futures,
          :files,
          :owned_drops
        ],
        do: raise(ArgumentError, "unknown Rust extraction option: #{key}")

    if Keyword.get(opts, :futures, :reject) == :immediate and
         Keyword.get(opts, :execution, :pure) != :pure,
       do: raise(ArgumentError, "immediate future extraction currently requires pure execution")

    if Keyword.get(opts, :futures, :reject) in [:polling, :suspending, :cancelling] and
         Keyword.get(opts, :execution, :pure) != :runtime,
       do: raise(ArgumentError, "stateful future polling requires runtime execution")

    if Keyword.get(opts, :owned_drops, false) == true and
         Keyword.get(opts, :execution, :pure) != :runtime,
       do: raise(ArgumentError, "owned destruction requires runtime execution")

    if Keyword.get(opts, :owned_drops, false) == :explicit and
         Keyword.get(opts, :execution, :pure) != :pure,
       do: raise(ArgumentError, "explicit ownership currently requires pure execution")

    file_models =
      Lynx.Rust.FileModels.enabled!(
        Keyword.get(opts, :files, :reject),
        Keyword.get(opts, :execution, :pure)
      )

    unwind = Keyword.get(opts, :unwind, :reject)
    Lynx.Rust.NativeUnwind.charon_arguments(unwind)

    if unwind == :assertions and Keyword.get(opts, :execution, :pure) != :runtime,
      do: raise(ArgumentError, "assertion unwind requires runtime execution")

    if unwind == :captured and
         {Keyword.get(opts, :execution, :pure), Keyword.get(opts, :owned_drops, false)} not in [
           {:pure, :explicit},
           {:runtime, false}
         ],
       do:
         raise(
           ArgumentError,
           "captured unwind requires pure explicit ownership or runtime execution without owned_drops"
         )

    Lynx.Rust.NativeUnwind.backend_arguments!(unwind, tools)

    if Enum.any?(
         [:rustler_encoders, :rustler_decoders],
         &(&1 in Keyword.get(opts, :external_calls, []))
       ),
       do: Lynx.Rustler.require_rustler!(context)

    discovery =
      describe!(
        context,
        tools,
        roots,
        output,
        module,
        Keyword.take(opts, [
          :external_types,
          :root_attribute,
          :mir,
          :unwind,
          :futures,
          :owned_drops
        ])
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
             Keyword.take(opts, [
               :external_types,
               :root_attribute,
               :mir,
               :unwind,
               :futures,
               :owned_drops
             ]),
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
          Keyword.take(opts, [
            :external_types,
            :root_attribute,
            :mir,
            :unwind,
            :futures,
            :owned_drops
          ]),
          Enum.map(caches, & &1.opaque_pattern)
        )
      else
        discovery
      end

    %{document: document, llbc: llbc, first_party: first_party, models: models} = discovery

    # Every surviving type use must retain its compiler identity even when its
    # first serialized value occurs in cleanup removed by a later pass.
    document =
      if Keyword.get(opts, :execution, :pure) == :runtime,
        do: Lynx.Rust.LLBCJson.restore_type_references!(document, document),
        else: document

    discovery = %{discovery | document: document}

    {document, rustler_constructors} =
      if Keyword.get(opts, :execution, :pure) == :pure and
           :rustler_decoders in Keyword.get(opts, :external_calls, []) and
           Lynx.Rustler.ErrorConstructors.needed?(document, first_party) do
        unless Enum.any?(
                 models,
                 &(&1.rust == "rustler::error::Error" and &1.lean == "Lynx.Rustler.DecoderError")
               ),
               do:
                 raise(
                   ArgumentError,
                   "Rustler BadArg requires its explicit opaque Error conversion model"
                 )

        layout_opts =
          Keyword.take(opts, [:root_attribute, :mir, :unwind, :futures, :owned_drops])
          |> Keyword.put(
            :external_types,
            Enum.reject(models, &(&1.rust == "rustler::error::Error"))
          )

        layout =
          describe!(
            context,
            tools,
            roots,
            output,
            module <> ".ErrorLayout",
            layout_opts,
            Enum.map(caches, & &1.opaque_pattern)
          )

        {lowered, proof} =
          Lynx.Rustler.ErrorConstructors.lower!(document, layout.document, first_party, module)

        {lowered,
         if(proof,
           do: Map.put(proof, :layout_fingerprint, Lynx.Rust.Fingerprint.file!(layout.llbc))
         )}
      else
        {document, nil}
      end

    runtime_call_models =
      Keyword.get(opts, :external_calls, []) ++
        if(unwind == :captured, do: [:captured_unwind_drops], else: []) ++
        file_models ++
        if Keyword.get(opts, :futures, :reject) in [:polling, :suspending, :cancelling],
          do: [:native_wakers],
          else: []

    {document, nonpanicking_borrows} =
      if Keyword.get(opts, :execution, :pure) == :runtime and unwind != :captured,
        do:
          Lynx.Rust.NativeBorrows.prune_owned_calls!(
            document,
            first_party,
            runtime_call_models
          ),
        else: {document, []}

    document =
      if nonpanicking_borrows != [],
        do: Lynx.Rust.LLBCJson.restore_constant_references!(document, discovery.document),
        else: document

    {document, cleanup_flags} =
      if Keyword.get(opts, :execution, :pure) == :runtime,
        do: Lynx.Rust.CleanupFlags.lower!(document, first_party),
        else: {document, []}

    {document, native_unwind} =
      if unwind == :assertions,
        do: Lynx.Rust.NativeUnwind.lower!(document, first_party),
        else: {document, []}

    document =
      if nonpanicking_borrows != [] or cleanup_flags != [] or native_unwind != [],
        do: Lynx.Rust.LLBCJson.restore_trait_references!(document, discovery.document),
        else: document

    document =
      if Keyword.get(opts, :execution, :pure) == :runtime and unwind == :captured,
        do: Lynx.Rust.NativePanicCapture.prepare!(document),
        else: document

    {document, native_drops} =
      if Keyword.get(opts, :execution, :pure) == :runtime,
        do: Lynx.Rust.NativeDropLowering.lower!(document, first_party, unwind: unwind),
        else: {document, []}

    {document, nonpanicking} =
      if Keyword.get(opts, :execution, :pure) == :runtime and unwind != :captured,
        do: Lynx.Rust.NativeUnwind.nonpanicking_drops!(document),
        else: {document, []}

    document =
      if native_drops != [] or nonpanicking != [],
        do: Lynx.Rust.LLBCJson.restore_trait_references!(document, discovery.document),
        else: document

    # A first-party callee may contain implicit native destruction. Only after
    # those sites are validated and lowered can the existing analysis certify
    # its callers as nonpanicking. Recheck their original unwind cleanup rather
    # than erasing a raw destructor or assuming that an opaque call is safe.
    {document, nonpanicking_after_drops} =
      if Keyword.get(opts, :execution, :pure) == :runtime and native_drops != [] and
           unwind != :captured,
         do:
           Lynx.Rust.NativeBorrows.prune_owned_calls!(
             document,
             first_party,
             runtime_call_models
           ),
         else: {document, []}

    native_unwind =
      nonpanicking_borrows ++
        cleanup_flags ++
        native_unwind ++
        nonpanicking ++
        nonpanicking_after_drops

    document =
      if native_drops != [] or native_unwind != [],
        do: Lynx.Rust.LLBCJson.restore_spans!(document, discovery.document),
        else: document

    backend_llbc =
      if native_drops == [] and native_unwind == [] and rustler_constructors == nil do
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

    requested_calls =
      Keyword.get(opts, :external_calls, []) ++
        if(unwind == :captured, do: [:captured_unwind_drops], else: []) ++
        file_models ++
        if(Keyword.get(opts, :futures, :reject) in [:polling, :suspending, :cancelling],
          do: [:native_wakers],
          else: []
        )

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
        rustler_atom_caches: {caches, module},
        rustler_constructors: rustler_constructors,
        explicit_ownership: Keyword.get(opts, :owned_drops, false) == :explicit
      )

    document = audit.document

    backend_llbc =
      if audit.explicit_ownership || unwind == :captured do
        path = Path.rootname(llbc) <> ".ownership.llbc"
        File.write!(path, Lynx.Rust.LLBCJson.encode_like!(document, llbc))
        path
      else
        backend_llbc
      end

    audit = Lynx.Rust.FormatModels.scope(audit, module)
    formatting_modules = Lynx.Rust.FormatModels.install!(audit.external_calls, output, module)

    models =
      models ++
        Lynx.Rust.MutexModels.type_models(audit.external_calls, module) ++
        Lynx.Rust.LockModels.type_models(audit.external_calls, module) ++
        Lynx.Rust.ResourceModels.type_models(audit.external_calls, module) ++
        Lynx.Rust.FileModels.type_models(audit.external_calls, module) ++
        Lynx.Rust.FileOpenModels.type_models(audit.external_calls, module) ++
        Lynx.Rust.FormatModels.type_models(audit.external_calls, module)

    if Enum.any?(audit.external_calls, fn {_, m} -> m[:native_resource_type] end) do
      unless File.read!(Path.join(tools, "lynx-toolchain")) =~ "global-names-v1",
        do:
          raise(ArgumentError, "resource extraction requires the pinned global-names-v1 backend")

      unless Lynx.Rustler.require_rustler!(context) == "0.39.0",
        do: raise(ArgumentError, "resource models require Rustler 0.39.0")
    end

    unless length(models) == MapSet.size(MapSet.new(models, & &1.rust)),
      do: raise(ArgumentError, "conflicting native Rust type models")

    audit = Map.put(audit, :external_types, models)
    audit = Lynx.Rust.BytesModels.scope(audit, module)
    audit = Lynx.Rust.FileModels.scope(audit, module)
    audit = Lynx.Rust.CollectionModels.scope(audit, module)
    codec_plan = Lynx.Rust.NativeCodecs.plan!(audit)

    {backend_document, compiler_drop_queries} = Lynx.Rust.LLBCJson.drop_query_metadata!(document)

    backend_document =
      if compiler_drop_queries == [],
        do: backend_document,
        else: Lynx.Rust.LLBCJson.restore_type_references!(backend_document, discovery.document)

    {backend_document, native_guard_storage} =
      Lynx.Rust.NativeGuardStorage.lower!(
        backend_document,
        audit,
        models,
        Keyword.get(opts, :futures, :reject)
      )

    # Aeneas also visits unused opaque declarations retained by discovery (for
    # example the drop helper requested before unreachable cleanup is pruned).
    # Supply their validated primitive names to prevent unnecessary axiom
    # templates. Only actual call dependencies belong in the verification report;
    # their scoped mappings take precedence over the unreferenced candidates.
    backend_calls = Map.merge(audit.available_external_calls, audit.external_calls)

    {backend_document, native_expect_aliases} =
      Lynx.Rust.ResultModels.lower_native_names!(backend_document, backend_calls)

    {backend_document, formatting_aliases} =
      Lynx.Rust.FormatModels.lower_names!(backend_document, audit)

    backend_llbc =
      if formatting_aliases == [] and compiler_drop_queries == [] and native_guard_storage == [] and
           native_expect_aliases == [] do
        backend_llbc
      else
        path = Path.rootname(llbc) <> ".aeneas.llbc"

        File.write!(path, Lynx.Rust.LLBCJson.encode_like!(backend_document, llbc))
        path
      end

    constructor_modules =
      Lynx.Rustler.ErrorConstructors.install!(rustler_constructors, output, module, models)

    model_args =
      if models == [] and map_size(backend_calls) == 0 do
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
                      "rust_pattern" => &1[:backend_rust_name] || &1.rust,
                      "extract_name" => &1.lean
                    }
                  ),
                "functions" =>
                  Enum.map(
                    Enum.reject(Map.values(backend_calls), & &1.builtin),
                    &Map.merge(
                      %{
                        "rust_pattern" =>
                          Lynx.Rust.NativeGuardStorage.pattern(
                            &1[:backend_rust_name] || &1.rust_name,
                            native_guard_storage
                          ),
                        "extract_name" => &1.lean,
                        "can_fail" => &1.can_fail,
                        "lift" => &1.lift
                      },
                      &1
                      |> Map.take([:keep_params, :keep_trait_clauses])
                      |> Map.new(fn {k, v} -> {Atom.to_string(k), v} end)
                    )
                  )
              },
              [
                Lynx.Rustler.EncoderModels.external_names(audit.external_calls),
                Lynx.Rustler.DecoderModels.external_names(audit),
                Lynx.Rust.ResourceModels.external_names(audit.external_calls),
                Lynx.Rust.FormatModels.external_names(audit.external_calls)
              ]
              |> Enum.reduce(%{}, fn names, combined ->
                Map.merge(combined, names, fn _key, left, right -> left ++ right end)
              end)
            )
          )
        )

        ["-external-names", path] ++
          if(models == [] and constructor_modules == [],
            do: [],
            else: [
              "-extra-includes",
              Enum.join(Enum.map(models, & &1.import) ++ constructor_modules, ",")
            ]
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

    translation =
      JSON.decode!(translation_bytes)
      |> Lynx.Rust.FormatModels.restore_report_names(formatting_aliases)

    translation_bytes =
      if formatting_aliases == [], do: translation_bytes, else: JSON.encode!(translation)

    implementations =
      Lynx.Rust.LLBC.link!(audit, translation,
        result_monad: result_monad,
        assertion_unwind_input: unwind == :assertions
      )

    Lynx.Rustler.AtomCaches.install!(cache_models, translation, output, module)
    Lynx.Rust.BytesModels.install!(audit, translation, output, module)

    operation_modules =
      Lynx.Rust.FileModels.install!(audit, translation, output, module) ++
        Lynx.Rust.CollectionModels.install!(audit, translation, output, module)

    codec_modules = Lynx.Rust.NativeCodecs.install!(codec_plan, translation, output, module)

    codec_hashes =
      Enum.map(
        [
          module <> ".Funs"
          | formatting_modules ++ codec_modules ++ operation_modules ++ constructor_modules
        ],
        fn name ->
          {name,
           Lynx.Rust.Fingerprint.file!(
             Path.join(output, String.replace(name, ".", "/") <> ".lean")
           )}
        end
      )

    # Keep per-root metadata, since several extractions can share one Lean package.
    File.write!(
      Path.join(output, String.replace(module, ".", "_") <> ".translation.json"),
      translation_bytes
    )

    %{
      audit: audit,
      explicit_ownership: audit.explicit_ownership,
      captured_unwind: audit.captured_unwind,
      reference_copies: audit.reference_copies,
      compiler_drop_queries: compiler_drop_queries,
      rustler_constructors: rustler_constructors,
      native_expect_aliases: native_expect_aliases,
      formatting_aliases: formatting_aliases,
      native_guard_storage: native_guard_storage,
      owned_drops: Keyword.get(opts, :owned_drops, false),
      resource_cleanup:
        for(
          type <- codec_plan,
          is_integer(type.native_cleanup),
          do: %{
            type_id: type["def_id"],
            function_id: type.native_cleanup,
            lean_name: Map.fetch!(implementations, type.native_cleanup)["lean_name"]
          }
        ),
      native_drops: native_drops,
      native_unwind: native_unwind,
      files: Keyword.get(opts, :files, :reject),
      futures: Keyword.get(opts, :futures, :reject),
      unwind: unwind,
      execution: execution,
      translation: translation,
      implementations: implementations,
      constants: Lynx.Rust.Constants.link!(audit.constants, translation),
      external_types: models,
      fingerprint:
        Lynx.Rust.Fingerprint.extraction!(context, tools, llbc, translation_bytes, first_party)
        |> then(fn digest ->
          Lynx.Rust.Fingerprint.digest(
            :erlang.term_to_binary(
              {digest, Lynx.Rust.Runtime.fingerprint(execution), codec_hashes, native_drops,
               rustler_constructors, Lynx.Rust.Fingerprint.file!(backend_llbc), unwind,
               native_unwind, models, requested_calls,
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
      audit_modules:
        Enum.uniq(
          [module <> ".Types", module <> ".Funs"] ++
            runtime_modules ++
            formatting_modules ++
            codec_modules ++
            operation_modules ++
            constructor_modules ++ Lynx.Rust.BytesModels.modules(audit, module)
        )
    }
  end

  # This stage discovers resolved Rust identities, including unsupported code.
  # It makes no verification claim. run!/6 always applies the full audit before
  # invoking Aeneas or producing an implementation/proof linkage.
  @doc false
  def describe!(context, tools, roots, output, module, opts \\ []) do
    for key <- Keyword.keys(opts),
        key not in [
          :external_types,
          :root_attribute,
          :mir,
          :unwind,
          :futures,
          :owned_drops,
          :opaque_functions,
          :excluded_functions,
          :item_roots
        ],
        do: raise(ArgumentError, "unknown Rust discovery option: #{key}")

    opaque = Keyword.get(opts, :opaque_functions, [])
    items = Keyword.get(opts, :item_roots, [])

    for {paths, label} <- [
          {items, "item roots"},
          {Keyword.get(opts, :excluded_functions, []), "excluded functions"}
        ] do
      unless is_list(paths) and
               Enum.all?(
                 paths,
                 &(is_binary(&1) and
                     Regex.match?(~r/\A[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)+\z/, &1))
               ),
             do: raise(ArgumentError, "invalid Rust metadata #{label}")
    end

    unless is_list(opaque) and
             Enum.all?(opaque, &is_binary/1) and
             Enum.all?(
               opaque,
               &Regex.match?(~r/^[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)+$/, &1)
             ),
           do: raise(ArgumentError, "invalid opaque Rust metadata function path")

    describe!(context, tools, roots, output, module, opts, opaque)
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

    attribute = Lynx.Rust.RootSelection.attribute!(Keyword.get(opts, :root_attribute))

    root_args =
      Lynx.Rust.RootSelection.arguments(roots, attribute, [context.artifact["target"]["name"]])

    # Metadata discovery also selects non-function items. Their consumers audit
    # the resolved identities; requested function roots retain the body check.
    root_args =
      root_args ++ Enum.flat_map(Keyword.get(opts, :item_roots, []), &["--start-from", &1])

    includes = Enum.flat_map(first_party, &["--include", &1])
    llbc = Path.join(output, String.replace(module, ".", "_") <> ".llbc")

    args =
      ["rustc", "--sysroot", "default"] ++
        Lynx.Rust.Futures.arguments!(Keyword.get(opts, :futures, :reject), tools) ++
        Lynx.Rust.NativeOwnedDrops.arguments!(Keyword.get(opts, :owned_drops, false), tools) ++
        Lynx.Rust.Mir.arguments!(opts) ++
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
          "--include",
          "core::io::seek::SeekFrom",
          "--dest-file",
          llbc
        ] ++
        root_args ++
        Lynx.Rust.DropModels.metadata_arguments(models) ++
        includes ++
        Enum.flat_map(Lynx.Rustler.EncoderModels.metadata_includes(models), &["--include", &1]) ++
        Enum.flat_map(Lynx.Rust.LibraryHelpers.includes(), &["--include", &1]) ++
        Enum.flat_map(models, &["--opaque", &1.rust]) ++
        Enum.flat_map(opaque, &["--opaque", &1]) ++
        Enum.flat_map(Keyword.get(opts, :excluded_functions, []), &["--exclude", &1]) ++
        ["--"] ++ Lynx.Rust.Cargo.extraction_arguments(context, output)

    diagnostics =
      run!(charon, args,
        cd: context.record["directory"],
        env: Lynx.Rust.Cargo.environment(context)
      )

    document = read_llbc!(llbc, diagnostics)
    validate_target!(document)

    Lynx.Rust.RootSelection.validate!(
      document,
      roots,
      attribute,
      [context.artifact["target"]["name"]],
      first_party
    )

    models =
      models ++
        Lynx.Rust.Futures.type_models!(Keyword.get(opts, :futures, :reject), document, module)

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
