module
public import Record.ConstructedLogProperties
public import Record.Extraction.RustlerAdapter
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.ConstructorAdapterProperties
set_option maxRecDepth 4096
open NativeFile Record.ConstructorLogProperties

attribute [local simp] NativeCodec.typeName NativeCodec.encode NativeMutex.typeName
  NativeResourceArc.typeName NativeResourceArc.handleType NativeResourceArc.termType

@[expose] def registered (env : Environment) : Environment :=
  {env with nativeResourceTypes := (env.nativeResourceTypes ++ [NativeResourceArc.typeName shared_log.LogResource]).eraseDups}

/-- The actual compiled constructor, resource encoder and owner cleanup return
term 8 from a filesystem-only starting heap, preserving the caller continuation. -/
theorem create_run {α : Type} (dispatcher : Dispatcher) (env : Environment) (script : Term) (next : Term → Result α) (choices : List ScheduleChoice) :
    ((Elixir.LynxIoFixture.Native.«log_create/0» dispatcher) >>= next).run (initial env script) choices =
      (next (.nativeReference 8)).run (constructed (registered env) script) choices := by
  let nativeNext := fun owner : NativeResourceArc shared_log.LogResource => do
    let term ← NativeResourceArc.encode owner
    NativeOwnedDrop.drop owner
    Result.ok term
  have traced := Rustler.executeNative_readyPrefix
    ((constructor_prefix (registered env) script).bind nativeNext) id
  have body := (traced.bind next).run choices
  simp only [Elixir.LynxIoFixture.Native.«log_create/0»,
    Elixir.LynxIoFixture.Native.«log_create:execution/0»,Rustler.withResourceTypes,
    Result.nativeModify_bind,Result.nativeModify_run]
  change (Rustler.executeNative (do
    let owner ← __CREATE__
    let term ← NativeResourceArc.encode owner
    NativeOwnedDrop.drop owner
    Result.ok term) id >>= next).run (initial (registered env) script) choices = _
  rw [body]
  simp only [Rustler.executeNative,Result.bind_ok,nativeNext,NativeOwnedDrop.drop,id_eq]
  rw [NativeResourceArc.newOwned_encode_release_framed_run payload _ next (mutexReady (registered env) script)
    (by simp [mutexReady,directory,registered,List.mem_eraseDups])
    (frame_below (registered env) script) choices]
  rfl

theorem create_next {α : Type} (dispatcher : Dispatcher) (env : Environment) (script : Term) (next : Term → Result α) :
    ((Elixir.LynxIoFixture.Native.«log_create/0» dispatcher) >>= next).run (initial env script) =
      next (.nativeReference 8) (constructed (registered env) script) := by
  exact create_run dispatcher env script next []

/-- The next NIF decodes the constructor's actual VM term and writes through
its capability. The whole continuation observes the verified updated heap. -/
theorem append_run {α : Type} (dispatcher : Dispatcher) (env : Environment) (next : Term → Result α) (choices : List ScheduleChoice) :
    ((Elixir.LynxIoFixture.Native.«log_append/2» dispatcher (.nativeReference 8) (.integer 13)) >>= next).run
      (constructed env Record.ConstructedLogProperties.input.script) choices =
      (next Term.true).run (Record.ConstructedLogProperties.returned (registered env) Record.ConstructedLogProperties.committed) choices := by
  have decoded := Record.ConstructedLogProperties.decoded_prefix (registered env)
    Record.ConstructedLogProperties.input.script
    (by simp [registered,List.mem_eraseDups])
  have head := decoded.bind (fun owner => Rustler.executeNative (__APPEND__ owner 13#u16) Rustler.encodeBool)
  have tail := Rustler.executeNative_readyPrefix (Record.ConstructedLogProperties.appended (registered env)) Rustler.encodeBool
  have joined := head.trans (by simpa only [Result.ok_bind,Record.ConstructedLogProperties.input,Record.LockedProperties.appendInput] using tail)
  have applied := (joined.bind next).run choices
  simp only [Rustler.executeNative_ok,Rustler.encodeBool] at applied
  simp [Elixir.LynxIoFixture.Native.«log_append/2»,Elixir.LynxIoFixture.Native.«log_append:execution/2»,
    Rustler.withResourceTypes,Result.nativeModify_bind,Result.nativeModify_run,Rustler.decodeUnsigned,Result.ofExcept,Result.handle]
  simpa [registered,constructed,mutexReady,directory,UScalar.ofNat,UScalar.ofNatCore,BitVec.ofFin_eq_ofNat] using applied

theorem append_next {α : Type} (dispatcher : Dispatcher) (env : Environment) (next : Term → Result α) :
    ((Elixir.LynxIoFixture.Native.«log_append/2» dispatcher (.nativeReference 8) (.integer 13)) >>= next).run
      (constructed env Record.ConstructedLogProperties.input.script) =
      next Term.true (Record.ConstructedLogProperties.returned (registered env) Record.ConstructedLogProperties.committed) := by
  exact append_run dispatcher env next []

/-- Both generated exports compose from a filesystem-only initial state. -/
theorem create_append_next {α : Type} (dispatcher : Dispatcher) (env : Environment) (next : Term → Result α) :
    ((do
      let resource ← Elixir.LynxIoFixture.Native.«log_create/0» dispatcher
      Elixir.LynxIoFixture.Native.«log_append/2» dispatcher resource (.integer 13)) >>= next).run
      (initial env Record.ConstructedLogProperties.input.script) =
      next Term.true (Record.ConstructedLogProperties.returned (registered (registered env)) Record.ConstructedLogProperties.committed) := by
  rw [bind_assoc]
  change ((Elixir.LynxIoFixture.Native.«log_create/0» dispatcher) >>= fun resource =>
    (Elixir.LynxIoFixture.Native.«log_append/2» dispatcher resource (.integer 13) >>= next)).run
      (initial env Record.ConstructedLogProperties.input.script) = _
  rw [create_next]
  exact append_next dispatcher (registered env) next

end Record.ConstructorAdapterProperties
