defmodule Lynx.Rust do
  @moduledoc """
  Verifies properties of first-party Cargo workspace implementations without Rustler.

  Roots are Rust paths, selected for extraction with their reachable first-party
  definitions. Proof modules contain ordinary Lean theorems over those generated
  definitions. The checked report discovers which implementations each theorem
  actually mentions; extracted bodies without properties are never called verified.

  The closed standard-library catalogue includes safe shared-slice indexing and
  `split_at`, and a UTF-8 model for `core::str::from_utf8` up to 4096 bytes with
  exact error offsets and sequence lengths. Larger inputs cause verification
  exhaustion. These standard-library operations are explicitly reported models,
  not proofs of Rust core's implementation. Other slice/string operations remain
  rejected unless separately supported.

  Fixed-width signed/unsigned integers from 8 through 128 bits also support
  `to_le_bytes`, `to_be_bytes`, `from_le_bytes` and `from_be_bytes` through
  Aeneas's existing bit-vector models. Admission checks the exact scalar,
  byte-array width, compiler identity and safe Rust signature. Native-endian
  conversions are not included. These are reported standard-library models.

  Vec shared/mutable slice views and bounds-checked mutable slice indexing reuse
  Aeneas's value and borrow-update models. Owned byte vectors using the standard
  Global allocator have an explicit logical deallocation model, including
  compiler-emitted cleanup paths. Drop erasure for custom allocators or element
  destructors is rejected. This does not admit vector growth or establish native
  allocation, capacity or deallocation correctness.
  """

  @doc """
  Builds, extracts and kernel-checks workspace properties.

  Required option `:roots` lists Rust paths. `:proof_modules` lists Lean modules
  containing properties; `:required_properties` can require particular theorem
  names, rejecting missing or unrelated theorems. Every supplied module is audited
  in full, including private and unused declarations.

  `:lean_project` defaults to `lynx-proofs` in the workspace and is initialized
  with the pinned runtime when needed. `:module_prefix` defaults to
  `Native.Extraction`. Also accepts `:tools` (or `LYNX_AENEAS_DIR`), `:build_dir`
  and `:cargo` options as in `Lynx.Rustler.prepare!/3`.

  `:execution` is `:pure` by default. `:runtime` interprets extracted computations
  using `Lynx.Result`, permitting composition with runtime effects. It requires
  the pinned result-monad backend. Native panic uses the internal `rust_panicked`
  marker; undefined behavior and divergence are verification exhaustion. This
  mode admits `std::sync::Mutex::new` with typed shared cells for bool/unsigned
  scalar payloads and monomorphic first-party structs of those scalars. Internal
  codecs are generated with kernel-checked roundtrips; they are not Rustler
  encoders or native memory layouts. Recursive, borrowed, generic and other
  payloads are rejected. Runtime extraction also admits blocking `Mutex::lock`
  acquisition with an owned guard in both normal and poisoned results. Acquisition
  atomically updates a shared cell; contention blocks on the existing scheduler.
  Recursive acquisition exhausts verification. Standalone synchronous execution
  contexts are mapped to local Lynx processes; this is not an OS thread identity
  or async task/migration model. Shared/exclusive guard borrows use validated
  Deref models and Aeneas's mutable-borrow reconstruction, including first-party
  callees. Borrowed-guard functions must have acyclic, nonpanicking implementation
  dependencies: mutable-borrow outputs on failure are unsupported. The updated
  guard is returned as a value; release and resource lifetimes remain unsupported,
  so this does not yet verify a complete critical section.
  Explicit `core::mem::drop` and compiler-generated local normal drops are also
  supported for owned Mutex<bool/unsigned scalar> values. These remove their
  cells; scalar payloads cannot invoke a custom destructor. Projected, user-defined
  and general unwind drops remain rejected. Native facade conversion, locks and
  general native unwind cleanup require separate validated semantics.
  Owners may move into actual extracted first-party callees when no other owner
  remains live in the caller. The callee undergoes the same lifetime audit;
  effects and post-consumption failures compose through the runtime monad.
  Assumed external contracts cannot satisfy this ownership-transfer check.

  `unwind: :assertions` additionally preserves compiler assertion cleanup for
  local owned Mutex<bool/unsigned scalar> values. It requires `execution: :runtime`
  and the pinned assertion-unwind backend. The default `:reject` retains the
  conservative lifetime boundary. In assertion mode, compiler cleanup is checked
  and lowered before propagating panic. Boolean drop flags are preserved; custom
  payload destructors and projected cleanup remain unsupported. Cleanup behind
  potentially panicking calls and mutable-reference outputs on failure are not
  implemented. Disabling fallible-operation resugaring can expose arithmetic
  forms the backend rejects; this mode does not imply general overflow cleanup.
  Unsupported recursive/trait combinations fail elaboration.
  """
  def verify!(workspace, package, opts) do
    Lynx.External.with_preparation_lock(fn -> do_verify!(workspace, package, opts) end)
  end

  defp do_verify!(workspace, package, opts) do
    allowed = [
      :roots,
      :proof_modules,
      :required_properties,
      :lean_project,
      :module_prefix,
      :tools,
      :build_dir,
      :cargo,
      :execution,
      :unwind
    ]

    for key <- Keyword.keys(opts),
        key not in allowed,
        do: raise(ArgumentError, "unknown Rust verification option: #{key}")

    roots = Keyword.fetch!(opts, :roots)
    tools = opts[:tools] || System.fetch_env!("LYNX_AENEAS_DIR")
    prefix = Keyword.get(opts, :module_prefix, "Native.Extraction")
    proofs = Keyword.get(opts, :proof_modules, [])
    directory = opts[:build_dir] || Path.join([Mix.Project.build_path(), "lynx", "rust", package])
    context = Lynx.Rust.Cargo.build!(workspace, package, directory, Keyword.get(opts, :cargo, []))

    project =
      Lynx.Rust.Project.ensure!(
        opts[:lean_project] || Path.join(context.workspace.root, "lynx-proofs"),
        prefix,
        tools
      )

    extraction =
      Lynx.Rust.Extraction.run!(context, tools, roots, project, prefix,
        execution: Keyword.get(opts, :execution, :pure),
        unwind: Keyword.get(opts, :unwind, :reject)
      )

    Lynx.Rust.Project.build!(project, [prefix <> ".Funs" | proofs])

    file =
      Lynx.Rust.Proofs.file!(extraction, proofs,
        required_properties: Keyword.get(opts, :required_properties, [])
      )

    files =
      Lynx.Translation.new(
        externals: [
          %Lynx.External{bindings: [], files: [file], fingerprint: extraction.fingerprint}
        ]
      )
      |> Lynx.Translation.assemble()

    reports = Lynx.Commands.verify!(project, files)

    unless Enum.all?(reports, &(&1.status == :ok)),
      do:
        raise(
          "Rust properties or proof audit failed:\n#{inspect(reports, pretty: true, limit: :infinity)}"
        )

    %{
      reports: reports,
      verification:
        Lynx.Rust.Report.build!(extraction, reports, source_dir: context.record["directory"]),
      extraction: extraction,
      context: context,
      project: project
    }
  end
end
