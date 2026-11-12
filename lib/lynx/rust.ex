defmodule Lynx.Rust do
  @moduledoc """
  Verifies properties of first-party Cargo workspace implementations without Rustler.

  Roots are Rust paths, selected for extraction with their reachable first-party
  definitions. Proof modules contain ordinary Lean theorems over those generated
  definitions. The checked report discovers which implementations each theorem
  actually mentions; extracted bodies without properties are never called verified.

  The closed standard-library catalogue includes safe shared-slice indexing and
  `split_at`, shared `input[start..end]` / `input[..end]` indexing with bounds
  panics, and a UTF-8 model for `core::str::from_utf8` with exact error
  offsets and sequence lengths, without an artificial protocol-size cutoff.
  These standard-library operations are explicitly reported models,
  not proofs of Rust core's implementation. Other slice/string operations remain
  rejected unless separately supported. Shared `input[start..]` indexing remains
  rejected: the pinned upstream failure model does not preserve its bounds panic.
  `RangeFrom::get` remains supported. Array and vector indexing must retain
  evidence for each delegated standard indexing method; opaque or missing
  dictionary dependencies are rejected.

  `sysroot: :full_mir` performs a separate metadata-only Cargo check against
  Charon's full-MIR Miri standard library, rebuilding target dependencies together.
  Host build scripts and procedural macros retain the native sysroot. The normal
  native build is retained; both builds use the same explicit target, resolved
  from Cargo configuration or the host. Matching package, features, profile and
  target are checked. Named targets are supported; custom target files are rejected. This opt-in mode currently requires pure execution. Its Miri library
  configuration and equivalence to the native standard library remain explicit
  trusted boundaries. The sysroot artifacts are included in proof fingerprints.

  Full-MIR extraction retains the actual standard slice `starts_with` body and
  captures both `PartialEq` methods, including explicit default selection.
  Scalar, shared-reference and slice comparison models retain checked method
  dictionaries and custom first-party comparator implementations. Missing method
  evidence is rejected; comparison failures and short-circuit order are preserved.

  Full-MIR extraction also retains `strip_prefix`, `strip_suffix` and the standard slice/array
  `SlicePattern::as_slice` bodies. Pattern dictionaries must resolve to matching
  checked method implementations; array lengths retain their separate constant
  identities. Exact returned slices and comparator failures can be proved across
  crates. Custom constant-generic pattern implementations remain unsupported.
  Delegated primitives such as `split_at` remain explicitly reported models.
  Prefix/suffix consumers can compose across workspace crates, with proofs of
  exact payload bytes, reconstruction and framing bounds.

  Shared `str::as_bytes`, `str::len` and `str::is_empty` reuse the existing
  Aeneas byte-slice representation. Views preserve bytes and lengths count bytes,
  including multi-byte Unicode text. The standard-library conversion and native
  layout remain reported models; owned/mutable strings and character-safe slicing
  are not included in this subset.

  Immutable named scalar-array constants, static shared scalar slices and
  promoted shared arrays retain their actual checked initializers across crate
  boundaries. This includes byte-string literals with zero or non-UTF-8 bytes.
  Array lengths must be literal usize values; mutable, nested and generic constant
  payloads remain rejected. Array views and endian conversions retain their
  existing reported standard-library models.

  Fixed-width signed/unsigned integers from 8 through 128 bits also support
  `to_le_bytes`, `to_be_bytes`, `from_le_bytes` and `from_be_bytes` through
  Aeneas's existing bit-vector models. Admission checks the exact scalar,
  byte-array width, compiler identity and safe Rust signature. Native-endian
  conversions are not included. These are reported standard-library models.

  Signed/unsigned 64-bit `checked_add` and `checked_mul` reuse Aeneas's fixed-width
  models: overflow returns `None`. Standard `Option` question-mark propagation
  uses explicit, reported enum models for `Try::branch` and `FromResidual` over
  `Option<Never>`. Exact enum layouts, signatures and trait identities are checked;
  custom Try implementations and payload-bearing residual replacements are rejected.
  Rust core's native implementation and invalid enum representations are outside
  these models' verified boundary.

  `Option::and_then` and `Result::map_err` support compiler-generated callbacks
  with empty environments, owned bool/fixed-width integer captures, or shared
  references to these scalars or their slices, including
  borrowed arguments with validated region-only lifetime bounds. Their reported
  standard-library models invoke the actual extracted callback on `Some`/`Err`
  and preserve `None`/`Ok` without invoking it. The skipped callback must have
  validated no-op destruction. Mutable references, references to non-scalar data,
  owned aggregates, generic captures and arbitrary FnOnce implementations remain
  rejected; callback panics remain Rust failures.

  Shared-slice `for item in slice` loops reuse Aeneas's existing `IntoIterator`
  conversion and `Iterator::next` models. Admission checks method forwarding,
  shared item lifetimes, the matching iterator dictionary and Option layout.
  The first-party loop body remains extracted; native iterator implementation
  and pointer layout remain reported external boundaries. Owning/mutable
  iterators and iterator combinators are not included in this subset.

  Vec shared/mutable slice views and bounds-checked mutable slice indexing reuse
  Aeneas's value and borrow-update models. Shared `Vec::len` observations support
  arbitrary element types with the standard Global allocator; this does not admit
  element destruction on those types. Empty `Vec::new` is independent of element
  layout. Bounded `push` supports primitive scalars and concrete struct/enum
  layouts of at most 4095 bytes on every selected 32/64-bit target, using the
  standard Global allocator. Generic or symbolic composite layouts are rejected.
  Unwind cleanup behind these validated nonpanicking calls is unreachable;
  ordinary drops and cleanup behind other calls are still audited separately.
  Scalar vectors support logical deallocation including compiler-emitted cleanup
  paths. Growth beyond
  262144 elements exhausts verification. A kernel-checked model theorem rules
  out catchable overflow panics within that bound. Structural destruction also
  supports monomorphic first-party structs/enums containing scalar/Copy data,
  String, shared references and Vec fields when actual compiler glue is captured
  and checked. Recursive glue may close only through finite owned Vec elements;
  each body and dictionary is checked, including every variant. Custom Drop
  implementations, allocators, opaque/missing element glue and unguarded cycles
  remain rejected. These are reported erasure audits, not Lean implementation
  theorems for destructors. Native allocation, stack exhaustion, capacity and
  deallocation correctness remain unverified.

  Concrete `Result<T, E>` cleanup checks the actual generated destructor at
  scalar, admitted Copy or logical String payload types. Generic payloads and
  observable destructors remain rejected. The shared `Result::is_ok` observer
  reuses an explicitly reported Aeneas model; native Rust core behavior and heap
  deallocation remain outside these implementation proofs.
  """

  @doc """
  Builds, extracts and kernel-checks workspace properties.

  Required option `:roots` lists Rust paths. Optional `:root_attribute` selects
  annotated local implementations and their reachable dependencies using Charon's
  attribute selector, avoiding its nested-path resolver. Every requested literal
  first-party workspace function path must resolve to one extracted body with
  either selection mode, including explicitly selected dependency functions. Ordinary trait
  implementation patterns continue to use path selection. This can be used with
  release binaries without Lynx's nested-function selection patch.

  Optional `:mir` selects `:promoted`, `:elaborated` or `:optimized` compiler MIR
  for pure extraction. It cannot override runtime or compiler-owned runtime extraction.

  `:external_types` and `:external_calls` select the existing extraction models
  for non-workspace dependencies. Type entries specify Rust/Lean names, an import
  and a boundary label; call selection is restricted to the closed catalogue.
  These are explicitly reported external semantic models, not verified native
  implementations. First-party bodies/types cannot be replaced with opaque
  models. Imported proof modules retain full axiom auditing and kernel checks.

  `owned_drops: :explicit` retains upstream precise destructor dictionaries in
  pure extraction. Generic consumers can compose with actual first-party Drop
  bodies, including panics. Supplied dictionaries must resolve to actual audited
  method bodies or reported compiler NoopDestruct primitives over supported
  closed types. Untracked dictionaries, opaque methods, raw pointer operations
  and unsupported dictionary shapes are rejected. Unwind paths must contain
  only storage retirement and resumption; observable cleanup and reconstructed
  fallible operations with owned locals are rejected. This mode uses unmodified
  extraction tools and does not establish native allocation, FFI, unwind cleanup
  or stateful destructor correctness. `owned_drops: true` retains the separate
  runtime-only compiler lowering.

  `unwind: :captured, owned_drops: :explicit` preserves borrowed updates on panic
  using the cleanup-preserving Charon installation (`--captured`). Aeneas and its
  Lean library remain unmodified. Fallible ordinary functions return an explicit
  `core.result.Result`: `Ok` contains the Rust return value; `Err ()` denotes panic
  after actual compiler cleanup. This is an exceptional-exit model, not a change
  to the native Rust API. Original and captured signatures appear in the report.
  Actual nonpanicking destructor bodies compose across crates. Pure captured
  functions require scalar or unit outputs and no type or trait parameters;
  indirect/external fallible calls, panicking cleanup, reconstructed overflow and
  bounds operations and generic/formatted panic payloads are rejected. This mode does not verify native exception
  unwinding, allocation or FFI correctness.

  `execution: :runtime, unwind: :captured` additionally supports compiler-validated
  standard MutexGuard and destructor-free Mutex cleanup. Aeneas needs its existing
  runtime-monad/effectful-call extensions; Charon must preserve assertion cleanup.
  The reconstructed guard payload is committed before unlocking and poisoning on
  panic. Disposing an unlocked poisoned mutex is supported. Entry is modelled as
  nonpanicking, including acquisition of incoming guards; nested cleanup calls,
  acquisitions during cleanup, user destructors
  and double panics remain rejected. Standard locks, physical thread context and
  native allocation remain explicitly reported external models. This mode selects
  elaborated MIR without compiler-owned resource/future lowering.

  Captured runtime cleanup also releases destructor-free Rustler ResourceArc
  owners, preserving other Rust aliases and VM pins. The payload requires the
  existing compiler drop query and default Resource callbacks; custom cleanup is
  rejected. Resource construction inside supported functions captures
  the modelled registration panic and follows the original caller cleanup. Its
  successful owned result remains tracked until consumed or released; unrelated
  caller-owned mutexes are disposed on either exceptional exit. Allocation and
  native unwinding remain trusted boundaries. Monomorphic fallible functions can
  return destructor-free ResourceArc values, retaining their original signatures
  for Rustler encoding. The runtime backend retains extracted type annotations
  for fresh record payloads. Other owned return types remain unsupported and
  unselected exports are reported explicitly.

  Compiler temporaries that copy a mutable reference without retagging can be
  normalized when their only use is a dereference in the immediately following
  scalar assignment. The original pointer target and write are preserved, and
  normalization records appear in `:explicit_ownership`. Other mutable-reference
  copy shapes remain subject to the backend's supported subset.

  Pure extraction admits the Aeneas logical heap `Box::new` model. Boxed trait
  construction additionally requires validated compiler vtable metadata: a
  monomorphic scalar-field struct, one extracted safe shared scalar-returning
  method or validated Rustler Encoder, and a callback-free drop shim. Use elaborated MIR to retain compiler
  drop elaboration. The resulting dictionary can compose actual extracted
  methods in proofs; executable Rust dynamic calls remain unsupported. Native
  vtable ABI, allocation success and reclamation remain reported assumptions.
  Catalogued Rustler String Encoder dictionaries additionally use the existing
  encoding and logical deallocation models after compiled vtable/shim validation;
  foreign implementation bodies remain unverified.

  `:proof_modules` lists Lean modules containing properties; `:required_properties`
  can require particular theorem names, rejecting missing or unrelated theorems. Every supplied module is audited
  in full, including private and unused declarations.

  `:lean_project` defaults to `lynx-proofs` in the workspace and is initialized
  with the pinned runtime when needed. `:module_prefix` defaults to
  `Native.Extraction`. Also accepts `:tools` (or `LYNX_AENEAS_DIR`), `:build_dir`
  and `:cargo` options as in `Lynx.Rustler.prepare!/3`.

  `files: :regular, execution: :runtime` admits checked standard `File::read`, `File::write`,
  `File::sync_all`, `File::set_len` and `Seek<File>::seek` calls over registered regular-file capabilities.
  Explicit and compiler-inserted destruction of an owned `File` is admitted after
  validating the compiler destructor dictionary. A `close` outcome consumes the
  capability on success or error and retains its disk state for crash reasoning.
  Close does not imply synchronization; Rust ignores its native close error.
  The default `:reject` admits none of these calls. The bounded model (1 MiB) distinguishes
  visible bytes, persistent bytes, offsets, partial writes, blocking and I/O errors.
  Explicit outcome scripts describe external choices; malformed choices exhaust
  verification. A successful sync persists visible contents and length. Earlier
  persistence may tear bytewise between old and visible images, without device
  corruption. These filesystem/device guarantees and native descriptor
  correspondence are external assumptions, reported with the verification result.
  Error identities are opaque; payloads and error inspection are unsupported.
  Explicit and compiler-inserted error destruction additionally require a unique
  live `rust:os-io-error` cell at that identity, within the environment's allocated
  reference range. Its `live` marker is host admission of a callback-free OS error
  whose std/allocator cleanup does not panic or mutate observable application
  state. Cleanup consumes the cell; stale, duplicate, wrong-type, custom-payload
  and unadmitted errors exhaust verification. Error payload reclamation and native
  correspondence remain reported assumptions. Application-created/custom error
  constructors and their arbitrary destructors are not admitted by this model.
  Read counts select a visible prefix; unread buffer bytes survive. Read errors
  preserve the buffer and offset in this bounded external model; these are explicit
  std/OS correspondence assumptions rather than verified native guarantees.
  Seeking preserves the extracted Start(u64), End(i64) and Current(i64) enum,
  computes signed offsets without wrapping, permits bounded positions beyond EOF,
  and leaves contents unchanged. Seek errors preserve position under the same
  explicit std/OS boundary. `NativeFile.crashImage` permits additional modeled
  persistence at power loss; `restart` admits that image in a fresh environment.
  Restart remains a host admission boundary. `File::open<&str>` additionally
  supports an explicitly admitted flat namespace of regular files: portable ASCII
  names of 1 through 255 bytes, shared inode contents and separate read-only
  handle offsets. Exact standard AsRef<Path> dictionaries are validated before
  erasure; custom conversions and owned path types are rejected. Namespace cell
  zero maps names to inode identities and scripts host opening outcomes. Opening
  errors consume their outcome without allocating a handle; two successful opens
  allocate distinct handles to the same inode. Unsupported paths, malformed
  namespace state and inconsistent outcomes exhaust verification. This verifies
  extracted opening/cleanup protocols against the model, not native pathname
  resolution or physical descriptor allocation.
  Locally constructed `std::fs::OpenOptions` builders additionally support `new`,
  `read`, `write` and `open<&str>`. Compiler metadata must confirm that the builder
  needs no destruction. The setters preserve their mutable self borrow and boolean
  arguments. Read/write mode opens an existing regular inode without creating or
  truncating it; its cursor is independent and its contents remain shared. The
  same standard path dictionaries are validated before erasure. Builders entering
  through first-party function arguments, including nested containers, are rejected
  because they could carry unmodelled flags. Append/create/truncate flags and OS
  extensions are unsupported calls; write-only and no-access modes exhaust
  verification. Standard builder semantics, permissions and std/OS/FFI
  correspondence remain reported external boundaries.
  `File::create_new<&str>` grants a fresh empty inode and read/write handle only
  for an absent name. It preserves existing contents on admitted errors and rejects
  a contradictory success outcome for an existing name. Namespace admission
  separately encodes visible names, the last synchronized checkpoint and pending
  snapshots, with at most 1024 names and 1024 pending snapshots. Creating the name
  records a pending snapshot without advancing the checkpoint; pending snapshots
  may also reach disk. Opening the admitted current directory `"."` creates a
  separate directory capability. Its successful `sync_all` advances the namespace
  checkpoint and clears pending snapshots, under an explicit filesystem/device
  assumption. An error preserves the last guaranteed checkpoint; closing consumes
  the capability without synchronizing names. Directory synchronization preserves
  every regular inode's byte images and cannot replace file synchronization.
  `NativeFile.filesystemCrashImage` admits a bounded flat filesystem crash image:
  each unsynchronized pathname may independently select a recorded version,
  including lost or partially persisted renames; file bytes independently use
  the existing tearing model. This deliberately does not assume an ordered prefix
  of metadata persistence. Every registered inode requires exactly one mask,
  in heap order, with at most 1024 inodes. Unknown paths, missing/duplicate choices
  and malformed state are rejected. `restartFilesystem` restores only admitted
  names and inode bytes, discards every old capability/process/resource/lock,
  and retains a ghost freshness high-water mark. Image admission, restart and
  filesystem/device correspondence remain explicit external boundaries. These
  operations permit proofs around actual extracted publication/opening code;
  they do not verify the operating system's reboot implementation.
  `std::fs::rename<&str, &str>` uses an explicit single-directory Unix-style
  atomic metadata model. Both standard path-conversion dictionaries are checked.
  Replacement preserves inode contents and existing open capabilities, including
  handles of an unlinked destination. Renaming two names of the same inode is a
  no-op. An I/O error may leave the rename applied or unapplied; callers cannot
  assume rollback. Changed names are pending, and rename does not advance the
  synchronization checkpoint. Filesystem atomicity and OS/FFI correspondence
  remain assumptions rather than verified native guarantees.
  Physical close/descriptor reclamation, descriptor cloning, physical durability,
  standalone unlink, unrestricted concurrent I/O and general crash injection
  remain unsupported. Compiler-checked resource payloads may own File and
  Mutex<File> fields with `owned_drops: true`; panic cleanup of live files remains
  rejected. This option verifies first-party protocols against the explicit model,
  not the operating system.

  Standard Result `?` propagation reuses Aeneas's Try/FromResidual primitives.
  Every residual conversion requires the concrete standard identity From
  dictionary; custom or unresolved error conversions remain unsupported. These
  primitives are reported Rust core models, not verified core implementations.

  Runtime extraction supports standard `u64::checked_mul` with overflow returning
  `None`, and nonpanicking integer casts in checked implementation dependencies.
  Integer widths and truncation remain in the extracted operations. The pinned
  `partial-discriminants-v1` backend can inspect an initialized enum tag after a
  payload has moved; ordinary whole-value and field reads retain their checks.
  Ownership analysis retains selected enum variants across repeated tests and
  invalidates that information on assignment or calls.

  Standard `Result::expect` and `Option::expect` have runtime models for successful
  payload transfer. Failed expectations exhaust verification: panic formatting,
  hooks and unwind for these calls remain unsupported. A proof cannot assume
  that an expectation succeeds or establish a panic contract through this cutoff.
  The shared-log fixture verifies writable reopening, bounded tail repair,
  synchronization and returning a Rustler resource under declared I/O outcomes.
  This does not establish arbitrary crash recovery or native binary/FFI correctness.

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
  Standard `Waker::noop` is a distinct, nonallocating model that discards wake
  requests and leaves the environment unchanged. `Context::from_waker` retains
  the supplied capability. Waiting on a no-op waker blocks unless cancellation
  is observed; no notification or progress is invented. Standard constructors,
  callback/vtable execution and physical Context layout remain trusted.
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
  to the logical frame; pointer escapes are rejected. Saved storage can retain
  multiple supported native owners in separate fields across suspension, and
  destruction consumes them through the checked destructor models. Slot removal uses Aeneas's existing mutable
  replacement primitive. Invalid state tags and missing saved owners exhaust
  verification. The owned-captures backend also retains one supported native
  capture in an optional initial slot, moves it into saved storage on suspension,
  and executes the actual compiler cleanup on unstarted or suspended cancellation.
  `owned_drops: true` allows the supported mutex-containing resource payloads.
  The pin-macro backend also supports ordinary consuming Rust callers using
  standard `pin!` to poll such a compiler future. It validates the actual macro
  expansion and complete helper body, links Future::poll to the actual coroutine
  implementation and preserves the wrapper's field destruction through the
  compiler cleanup body. Direct unsafe helper calls remain unsupported. A caller
  may retain only that same sole owned frame across the poll; panics with live
  native owners and additional caller-owned resources are rejected. Repeated
  borrowed `Pin::as_mut` polling is supported for standard mutable-reference
  pointers after validating the complete standard helper body. Custom pointer
  families remain excluded. Reborrows retain the same audited sole frame across
  polls; previous state-tag and ownership-emptiness facts are discarded. Standard
  mutable-reference DerefMut semantics and physical pinning remain trusted.
  Each saved field currently supports one native owner. Ownership must agree at
  branch joins and remain invariant across loop backedges; moving one field does
  not consume the remaining frame. Whole-frame moves preserve all its owners.
  Nested multi-owner saved fields, non-Unpin fields, general native executor
  correspondence and generated async NIF exports remain unsupported. Explicit
  synchronous Rustler facades can poll and cancel supported extracted futures.
  Native allocation, physical pinning, standard primitives and FFI retain their
  reported trusted boundaries.

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
  payloads may contain a supported mutex identity. Unregistered construction invokes
  the actual extracted structural destructor. Final-owner release atomically retires
  ownership and requires an explicit `Environment.nativeFinalizerMode` for observable
  cleanup. `.synchronous` assumes inline callback execution; `.deferred` queues a
  callback dispatched through `NativeResourceArc.runFinalizer`. The default
  `.unspecified` exhausts verification on observable final release. OTP does not
  guarantee destructor completion when release returns. Deferred dispatch uses native
  allocation identities and does not model VM threads as BEAM processes. This subset
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
  dependencies: mutable-borrow outputs on panic are unsupported. Structured loops
  can retain owners across checked nonpanicking operations; loop safety does not
  establish termination. Scalar-vector destruction reuses the structural drop
  audit before its unreachable unwind cleanup is omitted. Validated native
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
  Runtime `Mutex::try_lock` performs an atomic nonblocking attempt. A held lock
  returns `WouldBlock` without changing the logical heap or allocating a guard
  token, including recursive attempts. An available poisoned lock returns the
  acquired guard in `Poisoned`.
  The actual standard error enum and method signatures are validated; supported
  consumers must account for the acquired guard. Rust std, native threading,
  allocation and FFI remain reported boundaries.
  `branching: :duplicate` retains separate symbolic branch contexts for supported
  guard-bearing results returned across first-party crates. It requires the
  branch-duplication backend and can increase generated code size. The default
  `:join` keeps the existing extraction heuristic. Loop fixed-point joins and
  invariant checks are unchanged; unsupported cases still fail extraction.

  Runtime RwLock operations support shared readers and exclusive writers.
  A foreign writer blocks a read; a conflicting writer registers a typed request
  and waits for existing leases to be released. Acquisition retires only its own
  request atomically. New reads with a queued writer stop verification because
  OS admission priority is not represented. Self-conflicting acquisition and
  invalid requests also stop verification. These are logical execution contexts;
  native thread correspondence, FIFO ordering and OS fairness are not established.
  Such payloads may contain primitive-valued RwLock fields and nested admitted
  structs. Their logical lock identities remain shared across cloned handles and
  NIF calls. Final release or failed registration retires these logical cells
  through generated cleanup; this does not invent a Rust destructor or verify a
  VM callback. Unsupported payload fields and custom destruction remain rejected.
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
    validate_options!(opts)
    Lynx.External.with_preparation_lock(fn -> do_verify!(workspace, package, opts) end)
  end

  # Invalid options do not need to wait for an active proof build.
  defp validate_options!(opts) do
    allowed = [
      :roots,
      :root_attribute,
      :mir,
      :external_types,
      :external_calls,
      :proof_modules,
      :required_properties,
      :lean_project,
      :module_prefix,
      :tools,
      :build_dir,
      :cargo,
      :sysroot,
      :execution,
      :unwind,
      :futures,
      :branching,
      :files,
      :owned_drops
    ]

    for key <- Keyword.keys(opts),
        key not in allowed,
        do: raise(ArgumentError, "unknown Rust verification option: #{key}")

    Lynx.Rust.Sysroot.validate!(opts)
    Lynx.Rust.RootSelection.attribute!(opts[:root_attribute])
    Lynx.Rust.Mir.validate!(opts)
    Lynx.Rust.Branching.validate!(opts)
  end

  defp do_verify!(workspace, package, opts) do
    roots = Keyword.fetch!(opts, :roots)
    tools = opts[:tools] || System.fetch_env!("LYNX_AENEAS_DIR")
    prefix = Keyword.get(opts, :module_prefix, "Native.Extraction")
    proofs = Keyword.get(opts, :proof_modules, [])
    directory = opts[:build_dir] || Path.join([Mix.Project.build_path(), "lynx", "rust", package])

    context =
      Lynx.Rust.Cargo.build!(
        workspace,
        package,
        directory,
        Lynx.Rust.Sysroot.cargo_options!(opts, workspace)
      )

    context = Lynx.Rust.Sysroot.context!(context, workspace, package, directory, tools, opts)

    project =
      Lynx.Rust.Project.ensure!(
        opts[:lean_project] || Path.join(context.workspace.root, "lynx-proofs"),
        prefix,
        tools
      )

    extraction =
      Lynx.Rust.Extraction.run!(context, tools, roots, project, prefix,
        external_types: Keyword.get(opts, :external_types, []),
        external_calls: Keyword.get(opts, :external_calls, []),
        root_attribute: opts[:root_attribute],
        mir: opts[:mir],
        execution: Keyword.get(opts, :execution, :pure),
        unwind: Keyword.get(opts, :unwind, :reject),
        futures: Keyword.get(opts, :futures, :reject),
        branching: Keyword.get(opts, :branching, :join),
        files: Keyword.get(opts, :files, :reject),
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
