defmodule Lynx.Rustler do
  @moduledoc """
  Prepares verified native semantics for a Rustler facade in a Cargo workspace.

  The adapter supports booleans, signed/unsigned fixed-width integers through
  64 bits, tuples of zero through seven fields, and ordinary `Result<T, E>`
  values composed from those types. `NifResult<T>` and other signatures fail
  explicitly. Immutable `rustler::Binary<'_>` values can be passed and returned
  using an explicit FFI type model. The immutable `as_slice` accessor and standard
  slice length have explicitly reported external models; other Binary methods
  remain rejected.
  Rustler 0.38.0 or 0.39.0 and the pinned
  Charon/Aeneas toolchain are required; see `docs/rust-verification-investigation.md`.

  `prepare!/3` builds the selected library, discovers its compiled exports,
  extracts the original Rust bodies and their first-party dependencies, and
  kernel-checks the modelled decoding, execution and encoding boundary.
  It does not establish native machine-code, Rustler FFI or BEAM correctness.
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
    * `:required_properties` — theorem names that must mention actual extracted
      implementations in their statements. Missing or unrelated properties fail.

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
    Lynx.External.with_preparation_lock(fn -> do_prepare!(workspace, package, opts) end)
  end

  defp do_prepare!(workspace, package, opts) do
    allowed = [
      :lean_project,
      :module_prefix,
      :tools,
      :build_dir,
      :cargo,
      :only,
      :proof_modules,
      :required_properties
    ]

    for key <- Keyword.keys(opts),
        key not in allowed,
        do: raise(ArgumentError, "unknown Rustler verification option: #{key}")

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

    roots =
      for binding <- discovered.bindings do
        Enum.join(
          [context.artifact["target"]["name"] | binding["modules"]] ++
            ["_", "__INVENTORY", "nif_func", "wrapper", "_", binding["rust_name"]],
          "::"
        )
      end

    models =
      if Enum.any?(
           discovered.bindings,
           &(contains_binary?(&1["arguments"]) or contains_binary?(&1["result"]))
         ) do
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

    extraction =
      Lynx.Rust.Extraction.run!(context, tools, roots, project, prefix,
        external_types: models,
        external_calls: if(models == [], do: [], else: [:rustler_binary_as_slice])
      )

    bindings = Lynx.Rustler.Bindings.link!(discovered, extraction.audit, extraction.translation)

    Lynx.Rust.Project.build!(project, [bridge, prefix <> ".Funs" | proofs])

    external =
      Lynx.Rustler.Adapter.external!(bindings, extraction.implementations,
        proof_modules: proofs,
        bridge_module: bridge,
        implementation_module: prefix <> ".RustlerAdapter",
        fingerprint:
          Lynx.Rust.Fingerprint.digest(
            :erlang.term_to_binary(
              {extraction.fingerprint, compiled, Lynx.Rust.Fingerprint.file!(expanded)},
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
        |> Lynx.Rust.Report.rustler(bindings, rustler_version),
      project: project,
      library: native,
      native_binary_hash: Lynx.Rust.Fingerprint.file!(native),
      expanded: expanded,
      bindings: bindings,
      extraction: extraction,
      context: context,
      trusted_boundary: [
        "rustc, Charon and Aeneas extraction",
        "reproducible Cargo build and macro expansion",
        "Rustler #{rustler_version} wrapper, FFI, native code and BEAM",
        "configured native artifact is installed by the application loader",
        "Lean kernel and standard logical axioms"
      ]
    }
  end

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

  defp require_rustler!(context) do
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
