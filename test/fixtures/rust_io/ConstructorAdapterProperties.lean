module
public import Record.ConstructedLogProperties
public import Record.Extraction.RustlerAdapter
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.ConstructorAdapterProperties
set_option maxRecDepth 4096
open NativeFile Record.ConstructorLogProperties

attribute [local simp] NativeCodec.typeName NativeMutex.typeName
  NativeResourceArc.typeName NativeResourceArc.handleType NativeResourceArc.termType

@[expose] def registered (env : Environment) : Environment :=
  {env with nativeResourceTypes := (env.nativeResourceTypes ++ [NativeResourceArc.typeName shared_log.LogResource]).eraseDups}

attribute [local simp] NativeFile.writableHandleTypeName NativeFile.inodeTypeName
  NativeFile.namespaceTypeName NativeFile.closedDirectoryTypeName

/-- Allocation, VM pin creation and nonfinal Rust-owner release retain each
actual modeled transition and preserve the constructor's filesystem frame. -/
theorem resource_prefix (env : Environment) (script : Term) :
    Result.ReadyPrefix (do
      let owner ← NativeResourceArc.newOwned payload
      let term ← NativeResourceArc.encode owner
      NativeOwnedDrop.drop owner
      Result.ok term) (mutexReady (registered env) script)
      (.ok (.nativeReference 8)) (constructed (registered env) script) := by
  simp only [NativeResourceArc.newOwned, NativeResourceArc.new, Result.nativeGet_bind]
  apply Result.ReadyPrefix.nativeGet
  simp only [mutexReady, directory, registered, List.mem_eraseDups, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false, or_true, ite_true, Result.nativeGet_bind]
  apply Result.ReadyPrefix.nativeGet
  simp only [List.mem_eraseDups, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_true, ite_true, NativeM.allocate, Result.wait_bind]
  apply Result.ReadyPrefix.wait
  · simp [fileCells]
    exact ⟨rfl, rfl⟩
  simp only [Result.ofExcept, Result.ok_bind, bind_assoc, Result.wait_bind]
  apply Result.ReadyPrefix.wait
  · simp
    exact ⟨rfl, rfl⟩
  simp only [Result.ok_bind, NativeResourceArc.encode_eq, Result.nativeGet_bind]
  apply Result.ReadyPrefix.nativeGet
  simp [NativeResourceArc.ownership, NativeResourceArc.referenceLimit, NativeCodec.roundtrip]
  simp only [NativeResourceArc.clone, Result.nativeModify_bind]
  apply Result.ReadyPrefix.nativeModify
  · simp [NativeResourceArc.ownership, NativeResourceArc.referenceLimit, NativeCodec.roundtrip]
    exact ⟨rfl, rfl⟩
  simp only [Result.ofExcept, Result.ok_bind, NativeM.allocate, Result.wait_bind]
  apply Result.ReadyPrefix.wait
  · simp
    exact ⟨rfl, rfl⟩
  simp only [Result.ofExcept, Result.ok_bind, NativeOwnedDrop.drop, NativeResourceArc.releaseOwned,
    Result.nativeModify_bind]
  apply Result.ReadyPrefix.nativeModify
  · simp [NativeResourceArc.ownedState, NativeResourceArc.ownerState,
      NativeResourceArc.ownership, NativeResourceArc.referenceLimit, NativeCodec.roundtrip]
    exact ⟨rfl, rfl⟩
  simp only [Result.ok_bind]
  exact .refl _ _

/-- The actual compiled constructor, encoder and owner cleanup return term 8
from a filesystem-only starting heap, for every actual run. -/
theorem create_prefix (dispatcher : Dispatcher) (env : Environment) (script : Term) :
    Result.ReadyPrefix (Elixir.LynxIoFixture.Native.«log_create/0» dispatcher)
      (initial env script) (.ok (.nativeReference 8)) (constructed (registered env) script) := by
  let nativeNext := fun owner : NativeResourceArc shared_log.LogResource => do
    let term ← NativeResourceArc.encode owner
    NativeOwnedDrop.drop owner
    Result.ok term
  have head := Rustler.executeNative_readyPrefix
    ((constructor_prefix (registered env) script).bind nativeNext) id
  have tail := Rustler.executeNative_readyPrefix (resource_prefix env script) id
  have joined := head.trans (by simpa only [nativeNext] using tail)
  simp only [Elixir.LynxIoFixture.Native.«log_create/0»,
    Elixir.LynxIoFixture.Native.«log_create:execution/0», Rustler.withResourceTypes]
  apply Result.ReadyPrefix.nativeModify
  · rfl
  simpa [Rustler.executeNative_ok, nativeNext, initial, registered] using joined

theorem create_run {α : Type} (dispatcher : Dispatcher) (env : Environment) (script : Term)
    (next : Term → Result α) (choices : List ScheduleChoice) :
    ((Elixir.LynxIoFixture.Native.«log_create/0» dispatcher) >>= next).run (initial env script) choices =
      (next (.nativeReference 8)).run (constructed (registered env) script) choices := by
  simpa only [Result.ok_bind] using ((create_prefix dispatcher env script).bind next).run choices

theorem create_next {α : Type} (dispatcher : Dispatcher) (env : Environment) (script : Term) (next : Term → Result α) :
    ((Elixir.LynxIoFixture.Native.«log_create/0» dispatcher) >>= next).run (initial env script) =
      next (.nativeReference 8) (constructed (registered env) script) := by
  exact create_run dispatcher env script next []

/-- Decode the constructor's actual VM term and append through its capability,
retaining registration, file synchronization and resource-owner release. -/
theorem append_prefix (dispatcher : Dispatcher) (env : Environment) :
    Result.ReadyPrefix
      (Elixir.LynxIoFixture.Native.«log_append/2» dispatcher (.nativeReference 8) (.integer 13))
      (constructed env Record.ConstructedLogProperties.input.script) (.ok Term.true)
      (Record.ConstructedLogProperties.returned (registered env) Record.ConstructedLogProperties.committed) := by
  have decoded := Record.ConstructedLogProperties.decoded_prefix (registered env)
    Record.ConstructedLogProperties.input.script
    (by simp [registered, List.mem_eraseDups])
  have head := decoded.bind (fun owner => Rustler.executeNative (__APPEND__ owner 13#u16) Rustler.encodeBool)
  have tail := Rustler.executeNative_readyPrefix (Record.ConstructedLogProperties.appended (registered env)) Rustler.encodeBool
  have joined := head.trans (by simpa only [Result.ok_bind, Record.ConstructedLogProperties.input,
    Record.LockedProperties.appendInput] using tail)
  simp only [Elixir.LynxIoFixture.Native.«log_append/2»,
    Elixir.LynxIoFixture.Native.«log_append:execution/2», Rustler.withResourceTypes]
  apply Result.ReadyPrefix.nativeModify
  · rfl
  simpa [Rustler.decodeUnsigned, Result.ofExcept, Result.handle, Rustler.executeNative_ok,
    Rustler.encodeBool, registered, constructed, mutexReady, directory,
    UScalar.ofNat, UScalar.ofNatCore, BitVec.ofFin_eq_ofNat] using joined

theorem append_run {α : Type} (dispatcher : Dispatcher) (env : Environment)
    (next : Term → Result α) (choices : List ScheduleChoice) :
    ((Elixir.LynxIoFixture.Native.«log_append/2» dispatcher (.nativeReference 8) (.integer 13)) >>= next).run
      (constructed env Record.ConstructedLogProperties.input.script) choices =
      (next Term.true).run (Record.ConstructedLogProperties.returned (registered env) Record.ConstructedLogProperties.committed) choices := by
  simpa only [Result.ok_bind] using ((append_prefix dispatcher env).bind next).run choices

theorem append_next {α : Type} (dispatcher : Dispatcher) (env : Environment) (next : Term → Result α) :
    ((Elixir.LynxIoFixture.Native.«log_append/2» dispatcher (.nativeReference 8) (.integer 13)) >>= next).run
      (constructed env Record.ConstructedLogProperties.input.script) =
      next Term.true (Record.ConstructedLogProperties.returned (registered env) Record.ConstructedLogProperties.committed) := by
  exact append_run dispatcher env next []

/-- Both generated exports compose from a filesystem-only initial state. -/
theorem create_append_prefix {α : Type} (dispatcher : Dispatcher) (env : Environment)
    (next : Term → Result α) :
    Result.ReadyPrefix (do
      let resource ← Elixir.LynxIoFixture.Native.«log_create/0» dispatcher
      let result ← Elixir.LynxIoFixture.Native.«log_append/2» dispatcher resource (.integer 13)
      next result)
      (initial env Record.ConstructedLogProperties.input.script) (next Term.true)
      (Record.ConstructedLogProperties.returned (registered (registered env)) Record.ConstructedLogProperties.committed) := by
  have first := (create_prefix dispatcher env Record.ConstructedLogProperties.input.script).bind
    (fun resource => do
      let result ← Elixir.LynxIoFixture.Native.«log_append/2» dispatcher resource (.integer 13)
      next result)
  have last := (append_prefix dispatcher (registered env)).bind next
  exact first.trans (by simpa only [Result.ok_bind] using last)

theorem create_append_next {α : Type} (dispatcher : Dispatcher) (env : Environment) (next : Term → Result α) :
    ((do
      let resource ← Elixir.LynxIoFixture.Native.«log_create/0» dispatcher
      Elixir.LynxIoFixture.Native.«log_append/2» dispatcher resource (.integer 13)) >>= next).run
      (initial env Record.ConstructedLogProperties.input.script) =
      next Term.true (Record.ConstructedLogProperties.returned (registered (registered env)) Record.ConstructedLogProperties.committed) := by
  simpa only [bind_assoc] using (create_append_prefix dispatcher env next).run []

end Record.ConstructorAdapterProperties
