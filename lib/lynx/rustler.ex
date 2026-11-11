defmodule Lynx.Rustler do
  @moduledoc """
  Prepares verified native semantics for a Rustler facade in a Cargo workspace.

  The adapter supports booleans, signed/unsigned fixed-width integers through
  64 bits, tuples of zero through seven fields, and ordinary `Option<T>`/`Result<T, E>`
  values composed from those types. Options try the payload decoder first, then
  recognize `nil`; nested options therefore do not have an injective encoding.
  Return values can also contain monomorphic
  first-party structs/enums whose actual `Encoder` implementations can be
  extracted. Derived `NifTuple` return Encoders also use their actual expanded
  Rust implementations, with an explicit tuple-construction FFI model. This does
  not by itself enable derived argument Decoders. Pure custom argument Decoders
  use their actual extracted bodies with the supported primitive decoder models.
  The compiler resolves their types, encoder roots and generated atom
  caches automatically; no per-export Lean adapter or name mapping is required.
  Supported stateless runtime encoders include atoms, u64, strings, borrowed str,
  shared references, pairs and Vec. Pure custom arguments and `NifResult<T>` use
  extracted implementations and modelled return conversion; unsupported signatures
  fail explicitly. Immutable `rustler::Binary<'_>` values can be passed and returned
  using an explicit FFI type model. The immutable `as_slice` accessor and standard
  slice length have explicitly reported external models; other Binary methods
  remain rejected.
  `Vec<u8>` arguments and results, including tuple/result fields, use proper-list
  encoding and sequential element decoding through Rustler's u32-to-u8 narrowing
  conversion. Improper tails panic after preceding elements decode; an earlier
  invalid element returns badarg first. Byte-vector codecs have an explicit
  1,048,576-element verification bound; larger values produce exhaustion, not a
  simulated native decoding error. Native allocation within the bound is trusted.
  Scalar vectors also support bool and signed/unsigned fixed-width integers
  through 64 bits, including tuple/result/option fields. They use the same element
  budget and sequential list decoding; each element uses its ordinary scalar
  decoder, including Rustler's signed narrowing behavior. Other vector elements
  and custom allocators remain unsupported.
  Native environment/term handles, allocation and atom-cache initialization are
  explicitly reported FFI models. Strings longer than 4,294,967,295 bytes and
  lists longer than 2,147,483,647 elements exhaust verification. Generated atom
  caches currently must be in the facade crate's expanded source.
  Rustler 0.38.0 or 0.39.0 and the pinned
  Charon/Aeneas toolchain are required; install with `tools/setup-rust-verification.sh`.
  By default, `tools/setup-rust-verification.sh NEW_DIRECTORY`
  installs the hax-supported Aeneas release and Lean library without local patches
  or an OCaml/opam build. Charon carries only the nested-function resolver fix
  needed to select actual Rustler macro bodies. Select that directory with `:tools`
  or `LYNX_AENEAS_DIR`. This profile does not provide the custom bounded formatting
  library or native runtime extensions; install those explicitly with
  `tools/setup-rust-verification.sh --runtime NEW_DIRECTORY`.
  The execution model still defaults to `:pure` with either installation.

  `prepare!/3` builds the selected library, discovers its compiled exports,
  extracts the original Rust bodies and their first-party dependencies, and
  kernel-checks the modelled decoding, execution and encoding boundary.
  It does not establish native machine-code, Rustler FFI or BEAM correctness.
  Runtime scalar NIFs may allocate and release Rust-owned resources internally.
  Registration capabilities are derived from facade inventory records and the
  generated Rustler 0.39 default loader, checked against compiler-resolved types
  and the compiled entry's load-callback presence. Successful native loading,
  linker constructors and registration execution remain trusted FFI behavior.
  Custom loaders, named resource registrations, dependency-crate registrations
  remain unsupported. Top-level ResourceArc arguments and results are supported
  with runtime execution when their concrete payloads occur in audited
  new/clone/deref or consuming drop calls. Payloads are destructor-free by default; `owned_drops: true` also permits
  checked structural cleanup of directly owned mutex and File fields. No-drop
  payloads may also contain primitive-valued RwLock fields, shared across resource
  clones and successive NIF calls. Their derived logical retirement requires no
  handwritten adapter or Rust destructor; native lock, allocation and VM callback
  correspondence remain unverified. Encoding
  retains a logical VM pin and decoding acquires an independent Rust owner. VM pins stay
  live for the proof: garbage collection, process-death cleanup, serialization and
  distributed resource terms remain unsupported. Resource fields nested inside
  tuple/result codecs and unaudited signature-only resource payload discovery are
  rejected.
  Build scripts and procedural macros execute as part of the trusted build.
  Panic conversion requires an unwinding build; aborting builds are rejected.
  Integer decoding follows Rustler exactly, including its narrowing casts for
  8-bit and 16-bit inputs (decoded first through the 32-bit NIF API).
  """

  @doc "Prepares the `native: {Lynx.Rustler, options}` configuration used by law verification."
  def prepare!(opts) when is_list(opts) do
    prepare!(
      Keyword.fetch!(opts, :workspace),
      Keyword.fetch!(opts, :package),
      Keyword.drop(opts, [:workspace, :package])
    )
  end

  @doc """
  Prepares one Rustler facade and returns its external bundle and audit reports.

  Raw `rustler::Term` inputs use Rustler's identity Decoder, with native handle
  validity and environment copying at the explicit FFI boundary. In pure mode,
  `NifResult<T>` and `Result<T, rustler::Error>` return the successful payload
  directly, following Rustler's NifReturnable specialization. Supported decoder
  errors retain their original return/exception outcome. Pure BadArg and literal
  Atom/RaiseAtom construction are validated against the compiled enum and lowered
  to explicit foreign primitives. Atom names must be ASCII literals of at most
  255 bytes. Atom returns a value; RaiseAtom raises when converted on return.
  `Term`/`RaiseTerm` admit an owned boxed Encoder with an actual first-party
  implementation on a monomorphic scalar-field struct and callback-free compiler
  drop metadata. Owned String payloads additionally use the catalogued String
  Encoder and logical deallocation models, with validated compiled vtables and
  shims. The foreign String Encoder body is not claimed verified.
  Encoding is deferred until return conversion. A panic there
  escapes Rustler's computation catch and exhausts verification. Atom creation,
  allocation, native reclamation and FFI correctness remain trusted boundaries.
  Error inspection, other payload layouts and runtime NifResult conversion are
  rejected.

  Options:

    * `:lean_project` — a Lake project depending on Lynx and the pinned Aeneas
      runtime. Defaults to `lynx-proofs` in the workspace; missing projects are
      initialized with the runtime shipped by the pinned tools.
    * `:module_prefix` — namespace for extracted definitions; defaults to
      `Native.Extraction`. Use distinct prefixes for different roots in one project.

    * `:tools` — pinned tool directory, defaulting to `LYNX_AENEAS_DIR`.
    * `:build_dir` — verification-owned Cargo output directory; defaults under
      the current Mix build directory. The selected root is rebuilt each time.
    * `:cargo` — Cargo `:features`, `:default_features`, `:target`, `:profile`.
    * `:only` — nonempty list of exported `{name, arity}` pairs to verify, such as
      `[calculate: 1]`. Defaults to every export. Unselected NIF calls are rejected
      by Lynx; unsupported signatures outside this selection need no adapter.
    * `:proof_modules` — additional Lean property modules to build and audit.
    * `:proof_roots` — additional qualified first-party Rust function paths to extract
      alongside selected NIFs. These internal functions need not be NIF exports;
      their actual implementations and dependencies undergo the same checks.
    * `:root_attribute` — a qualified Rust tool attribute selecting annotated NIF
      implementations and their dependencies. Rustler preserves function attributes
      inside its generated wrapper. Requested bindings must still have actual bodies;
      missing annotations cannot fall back to assumed implementations. This permits
      release Charon binaries without the nested-function selection patch. Register
      the tool attribute on the pinned nightly compiler, preferably only for the
      verification build.
    * `:mir` — pure extraction MIR stage: `:promoted`, `:elaborated` or
      `:optimized`. Custom input Decoders default to `:elaborated`, retaining
      compiler drop elaboration. Their actual first-party bodies are extracted;
      temporary tuple-field vectors require a validated unconditional compiler Copy
      witness before their logical cleanup can be erased. The FFI models admit
      bounded tuple-field extraction, u64 decoding and opaque forwarding of
      its error. Pure BadArg and bounded ASCII literal Atom/RaiseAtom construction
      are validated against the actual enum metadata and literal provenance.
      Admitted boxed Term/RaiseTerm payloads retain their actual Encoder dictionary
      and deferred conversion. Error inspection, unadmitted payload layouts and
      runtime custom Decoders are rejected.
    * `:required_properties` — theorem names that must mention actual extracted
      implementations in their statements. Missing or unrelated properties fail.
    * `:branching` — `:join` by default, or `:duplicate` to retain separate symbolic
      branch contexts instead of joining them. Requires the branch-duplication
      backend. Loop joins and invariant checks remain enabled; duplicated
      continuations can increase generated code size.
    * `:execution` — `:pure` by default, or `:runtime` to retain modeled native
      state and blocking waits in Lynx's runtime. Runtime bindings use concurrent
      purity, preserve effects before panic and convert `rust_panicked` to
      `nif_panicked`. Top-level resource handles preserve shared identity through
      modeled VM pins; native task identity and custom return encoders remain
      unsupported in this mode. Ordinary scalar/tuple/result and
      byte-vector codecs retain their existing decoding rules and cutoffs.
    * `:owned_drops` — `false` by default. `:explicit` with pure execution retains
      upstream destructor dictionaries and actual first-party Drop bodies,
      including panics converted by the NIF adapter. Supplied dictionaries are
      checked against actual methods or explicitly reported compiler NoopDestruct
      primitives. This mode does not require compiler or Lean-library patches;
      NIF boundary codecs are limited to bools, fixed-width integers and their
      tuples/options/results, whose wrapper cleanup has no destructor effects.
      Observable unwind cleanup and reconstructed fallible operations with owned
      locals are rejected. Native allocation and wrapper/FFI correctness remain
      trusted boundaries. With runtime execution, `true` admits
      supported ResourceArc payloads that directly own mutex or File fields,
      using actual extracted structural cleanup. Result encoding and partial argument-decoding cleanup
      use the same owning dispatch as extracted Rust calls. VM pins survive
      temporary Rust owners; VM collection, custom destructor unwind and native
      binary/FFI correctness remain outside these proofs.
    * `:files` — `:reject` by default. `:regular` with runtime execution forwards
      the bounded regular-file model to Rust extraction. With `owned_drops: true`,
      structural resource cleanup may close directly owned File fields through
      their checked compiler destructors, including supported Mutex<File> cleanup.
      Checked opening, exclusive creation, rename and synchronization operations
      retain the same explicit namespace/OS/device model as standalone Rust proofs.
      Consuming an I/O error additionally requires an admitted callback-free OS-error
      capability; unknown or custom payload destructors exhaust verification.
      Native payload reclamation, std/allocator cleanup and OS/FFI correspondence
      remain explicit boundaries. Descriptor cloning and live-file panic cleanup
      remain unsupported.
    * `:futures` — forwarded to `Lynx.Rust`; defaults to `:reject`. Runtime
      modes allow ordinary synchronous NIFs to construct and explicitly poll
      supported first-party futures. Standard `Waker::noop` and
      `Context::from_waker` have separately reported models. No-op wake requests
      are discarded; Pending never implies completion. This does not generate
      async Rustler exports or establish a general native executor.
    * `:unwind` — `:reject` by default; `:assertions` selects the existing bounded
      mutex assertion-cleanup adapter for destructor-free payloads with runtime
      execution. Guard unwind and general failing-callee cleanup remain unsupported.

  The returned `:verification` separates extracted bodies, checked Rust properties,
  cross-crate composition and generated adapter correspondence theorems. It lists
  the exact checked statements, source locations, contracts used and trusted
  boundaries. `:reports` retains the ordinary runner audit reports.

  Pass the returned `:external` to `Lynx.Laws.verify/2` using the same
  `:lean_project`. Audit reports must all succeed before this function returns.
  Successful adapter audits and dependent laws reuse Lynx's proof cache. Cargo
  compilation and extraction still run to establish the current implementation.
  """
  def prepare!(workspace, package, opts) do
    execution = validate_options!(opts)

    Lynx.External.with_preparation_lock(fn ->
      do_prepare!(workspace, package, opts, execution)
    end)
  end

  # Invalid configuration must fail before waiting for another proof build.
  # Validation is pure; preparation still serializes all filesystem mutations.
  defp validate_options!(opts) do
    allowed = [
      :lean_project,
      :module_prefix,
      :tools,
      :build_dir,
      :cargo,
      :only,
      :proof_modules,
      :proof_roots,
      :root_attribute,
      :mir,
      :required_properties,
      :execution,
      :futures,
      :branching,
      :unwind,
      :owned_drops,
      :files
    ]

    for key <- Keyword.keys(opts),
        key not in allowed,
        do: raise(ArgumentError, "unknown Rustler verification option: #{key}")

    Lynx.Rust.RootSelection.attribute!(opts[:root_attribute])
    Lynx.Rust.Mir.validate!(opts)
    Lynx.Rust.Branching.validate!(opts)
    proof_roots = Keyword.get(opts, :proof_roots, [])

    unless is_list(proof_roots) and
             Enum.all?(proof_roots, fn root ->
               is_binary(root) and Regex.match?(~r/^[A-Za-z_][A-Za-z_0-9]*::.+$/, root)
             end),
           do: raise(ArgumentError, "proof_roots must be a list of qualified Rust function paths")

    execution = Keyword.get(opts, :execution, :pure)

    unless execution in [:pure, :runtime],
      do: raise(ArgumentError, "unsupported Rust execution model: #{inspect(execution)}")

    Lynx.Rust.FileModels.enabled!(Keyword.get(opts, :files, :reject), execution)

    owned = Keyword.get(opts, :owned_drops, false)

    unless {owned, execution} in [
             {false, :pure},
             {false, :runtime},
             {true, :runtime},
             {:explicit, :pure}
           ],
           do:
             raise(
               ArgumentError,
               "owned resource cleanup requires runtime execution for true; :explicit requires pure execution"
             )

    execution
  end

  defp do_prepare!(workspace, package, opts, execution) do
    prefix = Keyword.get(opts, :module_prefix, "Native.Extraction")
    tools = opts[:tools] || System.fetch_env!("LYNX_AENEAS_DIR")
    build_dir = opts[:build_dir] || Path.join([Mix.Project.build_path(), "lynx", "rust", package])
    proofs = Keyword.get(opts, :proof_modules, [])
    context = Lynx.Rust.Cargo.build!(workspace, package, build_dir, Keyword.get(opts, :cargo, []))
    rustler_version = require_rustler!(context)
    require_unwind!(context)

    project =
      Lynx.Rust.Project.ensure!(
        opts[:lean_project] || Path.join(context.workspace.root, "lynx-proofs"),
        prefix,
        tools
      )

    bridge = Lynx.Rustler.Bridge.install!(project, prefix)

    native =
      case Enum.filter(
             context.artifact["filenames"],
             &(Path.extname(&1) in [".dylib", ".so", ".dll"])
           ) do
        [native] -> native
        _ -> raise ArgumentError, "Rustler facade must build a single cdylib: #{package}"
      end

    expanded = Path.join(context.directory, "rustler-expanded.rs")
    File.write!(expanded, Lynx.Rust.Cargo.expand!(context))
    compiled = Lynx.Rustler.Metadata.inspect!(native)
    discovered = Lynx.Rustler.Metadata.bindings!(expanded, compiled, opts[:only])
    Lynx.Rustler.Bindings.validate_ownership!(discovered, Keyword.get(opts, :owned_drops, false))

    roots =
      for binding <- discovered.bindings do
        Enum.join(
          [context.artifact["target"]["name"] | binding["modules"]] ++
            ["_", "__INVENTORY", "nif_func", "wrapper", "_", binding["rust_name"]],
          "::"
        )
      end

    roots = Enum.uniq(roots ++ Keyword.get(opts, :proof_roots, []))

    binary? =
      Enum.any?(
        discovered.bindings,
        &(contains_binary?(&1["arguments"]) or contains_binary?(&1["result"]))
      )

    custom? = Enum.any?(discovered.bindings, &Lynx.Rustler.Bindings.custom?(&1["result"]))
    decoders? = Enum.any?(discovered.bindings, &Lynx.Rustler.Bindings.custom?(&1["arguments"]))
    returns? = Enum.any?(discovered.bindings, &Lynx.Rustler.Bindings.nif_result?(&1["result"]))
    term? = Enum.any?(discovered.bindings, &contains_term?/1)
    codecs? = custom? or decoders? or returns? or term?
    mir = opts[:mir] || if(decoders? or returns?, do: :elaborated)

    if execution == :runtime and decoders?,
      do: raise(ArgumentError, "runtime Rustler custom decoders are unsupported")

    models =
      if binary? do
        [
          %{
            rust: "rustler::types::binary::Binary",
            lean: "Lynx.Rustler.Binary",
            import: bridge,
            label:
              "Rustler 0.38/0.39 Binary decoded as immutable bytes at the unverified FFI boundary"
          }
        ]
      else
        []
      end

    models =
      models ++
        if(term?,
          do: [
            %{
              rust: "rustler::term::Term",
              lean: "Lynx.Rustler.NativeTerm",
              import: bridge,
              label:
                "Rustler raw Term identity/copy FFI model; native term handles, environments and allocation unverified"
            }
          ],
          else: []
        )

    {discovered, roots, models} =
      if codecs? do
        raw =
          Lynx.Rust.Extraction.describe!(context, tools, roots, project, prefix <> ".Discovery",
            external_types: models,
            root_attribute: opts[:root_attribute],
            mir: mir
          )

        resolved =
          Lynx.Rustler.Bindings.resolve!(discovered, raw.document, raw.first_party, models)

        codecs =
          for {rust, lean} <- [
                {"rustler::env::Env", "Env"},
                {"rustler::term::Term", "NativeTerm"},
                {"rustler::types::atom::Atom", "Atom"}
              ],
              do: %{
                rust: rust,
                lean: "Lynx.Rustler." <> lean,
                import: bridge,
                label:
                  "Stateless Rustler term-construction FFI model; handles, allocation and native runtime unverified"
              }

        # An extracted Encoder can itself call fallible term constructors.
        # Discovery of the facade signature need not have visited Error yet.
        errors = [
          %{
            rust: "rustler::error::Error",
            lean: "Lynx.Rustler.DecoderError",
            import: bridge,
            label:
              "Opaque Rustler Error conversion outcome for supported primitive codecs; forwarding, validated BadArg/ASCII literal atom and admitted deferred boxed Encoder construction; Error inspection unsupported"
          }
        ]

        {resolved,
         roots ++
           Lynx.Rustler.Bindings.encoder_roots(resolved) ++
           Lynx.Rustler.Bindings.decoder_roots(resolved),
         Enum.uniq_by(models ++ codecs ++ errors, & &1.rust)}
      else
        {discovered, roots, models}
      end

    custom? = Enum.any?(discovered.bindings, &Lynx.Rustler.Bindings.custom?(&1["result"]))
    returns? = Enum.any?(discovered.bindings, &Lynx.Rustler.Bindings.nif_result?(&1["result"]))
    mir = opts[:mir] || if(decoders? or returns?, do: :elaborated)

    if execution == :runtime and returns?,
      do: raise(ArgumentError, "runtime Rustler NifResult conversion is unsupported")

    if execution == :runtime and custom?,
      do: raise(ArgumentError, "runtime Rustler custom encoders are unsupported")

    extraction =
      Lynx.Rust.Extraction.run!(context, tools, roots, project, prefix,
        execution: execution,
        root_attribute: opts[:root_attribute],
        mir: mir,
        futures: Keyword.get(opts, :futures, :reject),
        branching: Keyword.get(opts, :branching, :join),
        files: Keyword.get(opts, :files, :reject),
        owned_drops: Keyword.get(opts, :owned_drops, false),
        unwind: Keyword.get(opts, :unwind, :reject),
        external_types: models,
        external_calls:
          if(binary?, do: [:rustler_binary_as_slice], else: []) ++
            if(custom? or decoders? or returns?, do: [:rustler_encoders], else: []) ++
            if(decoders? or returns?, do: [:rustler_decoders], else: []),
        rustler_atoms: if(custom?, do: :discover, else: [])
      )

    if rustler_version != "0.39.0" and
         Enum.any?(extraction.audit.external_calls, fn {_, model} ->
           model[:native_resource_type]
         end),
       do: raise(ArgumentError, "resource verification currently requires Rustler 0.39.0")

    registrations =
      Lynx.Rustler.Registrations.prepare!(
        extraction,
        context,
        tools,
        expanded,
        compiled,
        project,
        prefix
      )

    bindings =
      Lynx.Rustler.Bindings.link!(discovered, extraction.audit, extraction.translation,
        resource_types: registrations.types,
        result_monad: if(execution == :runtime, do: "Lynx.NativeM", else: "RustM"),
        assertion_unwind_input: Keyword.get(opts, :unwind, :reject) == :assertions
      )

    Lynx.Rust.Project.build!(project, [bridge, prefix <> ".Funs" | proofs])

    external =
      Lynx.Rustler.Adapter.external!(bindings, extraction.implementations,
        execution: execution,
        owned_drops: Keyword.get(opts, :owned_drops, false),
        logical_resource_cleanup:
          Lynx.Rust.ResourceLifetimes.enabled?(extraction.audit.translated),
        resource_types: Enum.map(registrations.types, & &1.tag),
        audit_modules: extraction.audit_modules,
        proof_modules: proofs,
        bridge_module: bridge,
        implementation_module: prefix <> ".RustlerAdapter",
        fingerprint:
          Lynx.Rust.Fingerprint.digest(
            :erlang.term_to_binary(
              {extraction.fingerprint, compiled, Lynx.Rust.Fingerprint.file!(expanded),
               registrations.fingerprint},
              [:deterministic]
            )
          )
      )

    property_file =
      Lynx.Rust.Proofs.file!(extraction, proofs,
        imports: Enum.map(external.files, & &1["module"]),
        required_properties: Keyword.get(opts, :required_properties, [])
      )

    external = %{external | files: external.files ++ [property_file]}
    files = Lynx.Translation.new(externals: [external]) |> Lynx.Translation.assemble()
    reports = Lynx.Commands.verify!(project, files)

    unless Enum.all?(reports, &(&1.status == :ok)),
      do:
        raise(
          "native adapter or proof audit failed:\n#{inspect(reports, pretty: true, limit: :infinity)}"
        )

    %{
      external: external,
      reports: reports,
      verification:
        Lynx.Rust.Report.build!(extraction, reports, source_dir: context.record["directory"])
        |> Lynx.Rust.Report.rustler(bindings, rustler_version)
        |> Map.put(:resource_registration, registrations)
        |> Map.update!(
          :trusted_boundary,
          &(&1 ++ if(registrations.boundary, do: [registrations.boundary], else: []))
        ),
      resource_registration: registrations,
      project: project,
      library: native,
      native_binary_hash: Lynx.Rust.Fingerprint.file!(native),
      expanded: expanded,
      bindings: bindings,
      extraction: extraction,
      context: context,
      trusted_boundary:
        [
          "rustc, Charon and Aeneas extraction",
          "reproducible Cargo build and macro expansion",
          "Rustler #{rustler_version} wrapper, FFI, native code and BEAM",
          "configured native artifact is installed by the application loader",
          "Lean kernel and standard logical axioms"
        ] ++
          if(registrations.boundary, do: [registrations.boundary], else: []) ++
          Lynx.Rustler.ErrorConstructors.boundary(extraction.rustler_constructors)
    }
  end

  defp contains_term?("term"), do: true
  defp contains_term?(values) when is_list(values), do: Enum.any?(values, &contains_term?/1)

  defp contains_term?(value) when is_map(value),
    do: Enum.any?(Map.values(value), &contains_term?/1)

  defp contains_term?(_), do: false

  defp contains_binary?("binary"), do: true
  defp contains_binary?(values) when is_list(values), do: Enum.any?(values, &contains_binary?/1)

  defp contains_binary?(value) when is_map(value),
    do: value |> Map.values() |> Enum.any?(&contains_binary?/1)

  defp contains_binary?(_), do: false

  defp require_unwind!(context) do
    cfg = Lynx.Rust.Cargo.replay!(context, context.record["arguments"] ++ ["--print", "cfg"])

    unless ~s(panic="unwind") in String.split(cfg, "\n"),
      do:
        raise(
          ArgumentError,
          "Rustler panic conversion requires a panic=unwind build; panic=abort is unsupported"
        )
  end

  @doc false
  def require_rustler!(context) do
    versions =
      for dep <- context.package.resolved_dependencies,
          package = context.workspace.packages[dep["pkg"]],
          package["name"] == "rustler",
          do: package["version"]

    unless versions in [["0.38.0"], ["0.39.0"]],
      do:
        raise(
          ArgumentError,
          "native adapter requires a direct Rustler 0.38.0 or 0.39.0 dependency; found #{inspect(versions)}"
        )

    hd(versions)
  end
end
