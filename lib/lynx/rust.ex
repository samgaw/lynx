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

  `:futures` defaults to `:reject`. Selecting `:immediate` extracts actual async
  constructors and compiler-generated poll bodies, including completed-state panic
  checks and first-party callees. It requires the pinned immediate-futures backend
  and pure execution. Suspension points and captures requiring destruction are
  rejected. The unused task Context is an explicitly reported Unit abstraction;
  waker access, cancellation, executors and resource ownership across suspension
  are not supported. Pin's data definition is extracted rather than supplied by
  an axiom. This does not verify physical pinning, native memory or an executor.

  `:futures` may also be `:polling` with `execution: :runtime`. This supports
  explicit calls to first-party Future implementations, including Pending/Ready
  results and registered wake requests. Context::waker and Waker::wake_by_ref
  have separately reported models. A wake capability requires a unique typed
  notification cell within the environment's reference counter; missing or invalid
  capabilities exhaust verification. Requests atomically mark that cell and may
  coalesce. The callback must be registered to this nonpanicking notification
  protocol. Registration, native vtables and callback implementation remain trusted
  boundaries; an arbitrary Waker cannot be assumed to satisfy that protocol.
  This does not introduce an executor, implicit repolling, fairness, external
  cancellation delivery or compiler-generated coroutine suspension. Pin::get_mut's
  actual compiled body is retained with a checked final mutable-borrow transfer.
  Safe Pin::new on a mutable Unpin reference is inlined only after checking the
  complete standard constructor body and actual pointer/pointee types. Ordinary
  first-party Rust callers can therefore construct and explicitly poll supported
  futures. Unsafe pinning helpers and other Pin operations are not implicitly admitted.

  `futures: :suspending, execution: :runtime` additionally extracts compiler
  coroutine suspension with saved fields. Captures and saved fields requiring
  destruction are rejected. Saved pointees must be Unpin. The logical state
  retains empty or initialized saved slots rather than assigning values to
  uninitialized memory. Reading an empty slot exhausts verification. The compiler's
  private Context pointer round-trip is validated and represented as a borrow;
  other pointer observations and escapes are rejected. This supports explicit
  polling, not an executor, cancellation cleanup or guards across suspension.

  `futures: :cancelling, execution: :runtime` also extracts the compiler's actual
  coroutine destruction body. Its self-pointer accesses become consuming accesses
  to the logical frame; pointer escapes are rejected. Saved storage can retain one
  supported native owner across suspension, and destruction consumes it through
  the checked destructor model. Slot removal uses Aeneas's existing mutable
  replacement primitive. Invalid state tags and missing saved owners exhaust
  verification. The owned-captures backend also retains one supported native
  capture in an optional initial slot, moves it into saved storage on suspension,
  and executes the actual compiler cleanup on unstarted or suspended cancellation.
  `owned_drops: true` allows the supported mutex-containing resource payloads.
  Multiple simultaneously live native owners per frame, non-Unpin fields,
  native executor integration and async NIF composition remain unsupported. Native allocation, physical pinning, standard primitives and FFI
  retain their reported trusted boundaries.

  `Lynx.NativeTask.drive` can execute a concrete extracted poll/destructor pair
  in the logical runtime. Pending tasks wait for an atomic wake consumption or
  caller-specified cancellation observation before another poll. The updated
  Context is retained; completion and between-poll cancellation invoke the actual
  destructor. Returned values and cancellation are distinct, and exhausted poll
  budgets never count as successful completion. This is an explicit executor
  policy model: native executor/callback correspondence and cancellation delivery
  remain trusted boundaries. Async Rustler binding generation is still unsupported.

  Saved `std::sync::MutexGuard` values are also supported in cancelling mode
  for the existing destructor-free payload subset. Actual first-party mutations
  before suspension are retained in the guard view and committed by normal
  release or cancellation. The original LLBC is audited before the opaque guard
  is represented as a `NativeGuard` capability without Rust lifetime arguments.
  Explicit shared/exclusive guard borrows, nominal type identities and executable
  bodies remain intact. Compiler poll inputs use path-sensitive ownership checks,
  so completed-state panics are distinguished from failures with a live guard.
  Panic/unwind with a live saved guard, native thread migration, executor behavior
  and other guard families remain unsupported. Rust memory safety, standard
  primitives, physical pinning, allocation and FFI remain trusted boundaries.

  `owned_drops: true, execution: :runtime` additionally extracts consuming drop
  entries for reached monomorphic structs requiring destruction. These use actual
  optimized compiler drop MIR after checked self-pointer normalization. Unsupported
  field destructors and native operations remain rejected. Rust-owned ResourceArc
  payloads may contain a supported mutex identity: final release and unregistered
  construction invoke the actual extracted structural destructor. This subset
  requires default Resource callbacks and nonpanicking mutex field cleanup;
  custom Drop, poisoned/held mutex destruction and VM collection remain unsupported.
  `Lynx.Rustler.prepare!/1` supports the same opt-in for top-level resource NIF
  arguments/results, including cleanup after a later argument fails conversion.
  VM collection and native FFI execution remain explicit trusted boundaries.

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
  dependencies: mutable-borrow outputs on panic are unsupported. Validated native
  models may block or exhaust verification without raising a catchable panic;
  neither case can establish successful completion. The updated
  guard is returned as a value. Explicit and compiler-generated normal guard
  release commit the reconstructed payload and unlock the uniquely owned cell,
  preserving poison status. Acquisition tokens and execution contexts are checked.
  Actual owning updates can compose with reacquisition across crates. Unreachable
  compiler cleanup behind certified nonpanicking calls is recorded and omitted;
  guard destruction during unwind remains unsupported.
  Explicit `core::mem::drop` and compiler-generated local normal drops are also
  supported for owned Mutex<bool/unsigned scalar> values and monomorphic
  first-party structs with supported native codecs when Charon's compiler query
  certifies `needs_drop = false`. Missing, unknown or true queries reject struct
  cleanup; fields alone never establish the absence of a user destructor. Install
  the pinned `needs-drop-v1` Charon patch for this metadata. These operations remove
  their cells without invoking a payload destructor. Projected, user-defined
  and general unwind drops remain rejected. General native unwind cleanup
  requires separate validated semantics.
  Rustler 0.39 `ResourceArc` allocation, clone, immutable dereference, explicit
  release and local scope cleanup are supported for monomorphic first-party
  payloads with native codecs and compiler-certified `needs_drop = false`.
  Concrete Resource dictionaries must inherit the default callbacks and flags.
  Resource payloads share a heap identity; each Rust-owned handle has a distinct
  consuming token. Properties must state loader registration explicitly using
  `Environment.nativeResourceTypes`; this does not verify compiled registration.
  Reference counts have a 1024-owner verification bound. The runtime models
  aggregate VM pins, stable resource-term identities and fresh Rust ownership on
  decoding. Collection, owner death, serialization and custom callbacks remain
  unsupported. Resource extraction
  requires the pinned `global-names-v1` backend. Rustler adapters can supply
  registration capabilities for facade-declared resources after checking the
  generated default loader, inventory constructors and compiler-resolved types.
  Custom loaders, named registrations and dependency-crate registrations remain
  unsupported. Runtime adapters support top-level ResourceArc arguments/results
  for payloads identified by audited resource operations in the selected extraction;
  nested resource codecs and signature-only payload discovery remain rejected.
  Owners may move into actual extracted first-party callees. When other owners
  remain live, the callee must also be certified nonpanicking. Every callee
  undergoes the same lifetime audit; supported effects compose through the
  runtime monad without losing retained ownership on failure.
  Assumed external contracts cannot satisfy this ownership-transfer check.

  Normal branches are audited independently and must consume or return every
  owner, with consistent ownership at joins. A single-field enum variant can
  transfer its complete owned payload; partial moves from multiple-field variants
  remain unsupported. The validated `PoisonError::into_inner` model transfers
  ownership without clearing poison, allowing complete critical sections to
  compose acquisition, explicit poisoned-result recovery, checked mutation and
  normal release across first-party crates. Panicking unwrap and guard unwind
  remain unsupported. Public runner trace lemmas support two finite contending
  schedules with two workers, each acquiring and releasing once. Actual extracted
  critical sections have parametric proofs preserving both successful updates
  under those schedules. This does not establish arbitrary-schedule safety,
  fairness, general liveness or native task identity. `Lynx.Rustler` runtime
  adapters can compose supported scalar and immutable resource interfaces with
  these effects; effectful custom encoders remain unsupported.

  `unwind: :assertions` additionally preserves compiler assertion cleanup for
  local owned mutexes with the same destructor-free payload subset. It requires `execution: :runtime`
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
      :unwind,
      :futures,
      :owned_drops
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
        unwind: Keyword.get(opts, :unwind, :reject),
        futures: Keyword.get(opts, :futures, :reject),
        owned_drops: Keyword.get(opts, :owned_drops, false)
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
