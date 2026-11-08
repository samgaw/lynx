module
public import Record.FramedLogProperties
public import Record.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.NativeLogProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LockedProperties Record.SharedLogProperties Record.FramedLogProperties

attribute [local simp] NativeCodec.typeName NativeCodec.encode NativeMutex.typeName
  NativeFile.typeName NativeResourceArc.typeName NativeResourceArc.handleType NativeResourceArc.termType

@[expose] def pinnedFrame := NativeResourceArc.vmCells logPayload 3 5 6

@[expose] def decodedFrame : List (Nat × String × Term) :=
  (7, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3) ::
    pinnedFrame.map fun cell => if cell.1 == 3 then
      (3, NativeResourceArc.typeName shared_log.LogResource,
        .tuple #[.integer 2, NativeCodec.encode logPayload]) else cell

@[expose] def pinned (env : Environment) (state : State) : Environment :=
  framedEnv env 6 pinnedFrame (Record.FramedLogProperties.free false) state

@[expose] def decoded (env : Environment) (counter : Nat) (state : State) : Environment :=
  framedEnv env counter decodedFrame (Record.FramedLogProperties.free false) state

@[expose] def returned (env : Environment) (state : State) : Environment :=
  framedEnv env 8 pinnedFrame (Record.FramedLogProperties.free false) state

theorem pin (env : Environment) (state : State) :
    NativeResourceArc.Pinned logPayload 3 5 6 (pinned env state) := by
  constructor
  · simp [pinned, framedEnv]
  · intro cell member
    simp only [pinned, framedEnv, pinnedFrame, NativeResourceArc.vmCells,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [pinned, framedEnv]
  all_goals simp [pinned, framedEnv, pinnedFrame, NativeResourceArc.vmCells]

/-- The actual Rustler decoder creates a fresh Rust owner alongside the VM pin. -/
theorem decode_prefix (env : Environment) (state : State)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ env.nativeResourceTypes) :
    Result.ReadyPrefix (NativeResourceArc.decode (.nativeReference 6)) (pinned env state)
      (.ok (⟨3,7⟩ : NativeResourceArc shared_log.LogResource)) (decoded env 7 state) := by
  have trace := NativeResourceArc.decode_pinned_prefix logPayload (pinned env state) 3 5 6
    (pin env state) registered
  simpa [pinned, decoded, framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells] using trace

/-- Append preserves the decoded registry, writes the actual encoded record,
synchronizes it and releases the file guard before returning. -/
theorem append_prefix (env : Environment) (data : ByteArray) (value : U16)
    (position : Nat) (rest : Term) (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) :
    Result.ReadyPrefix (shared_log.append ⟨3,7⟩ value) (decoded env 7 (appendInput data position rest))
      (.ok (.Ok true)) (decoded env 8 (appended (appendInput data position rest) value rest)) := by
  have borrowed := borrow_prefix (⟨3,7⟩ : NativeResourceArc shared_log.LogResource) logPayload value 2
    (decoded env 7 (appendInput data position rest)) (by decide) (by decide)
    (by simp [decoded, framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [decoded, framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [decoded, framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
  have critical := (Record.FramedLogProperties.append_success env 7 decodedFrame false data value position rest
    (by decide) (by simp [Apart, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [Apart, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [decodedFrame, pinnedFrame, NativeResourceArc.vmCells]) fits offset).1
  exact borrowed.trans critical

/-- Nonfinal owner release preserves the open file and the surviving VM pin. -/
theorem release_prefix (env : Environment) (state : State) :
    Result.ReadyPrefix (NativeOwnedDrop.drop (⟨3,7⟩ : NativeResourceArc shared_log.LogResource))
      (decoded env 8 state) (.ok ()) (returned env state) := by
  have trace := NativeResourceArc.releaseOwned_retained_prefix
    (⟨3,7⟩ : NativeResourceArc shared_log.LogResource) logPayload (decoded env 8 state)
    (by simp [decoded, framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [decoded, framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [decoded, framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
  simpa [NativeOwnedDrop.drop, returned, decoded, framedEnv, decodedFrame, pinnedFrame,
    NativeResourceArc.vmCells, List.filter] using trace

/-- The actual compiled export acknowledges after append synchronization and
consumes its decoded Rust token while retaining the VM-owned file resource. -/
theorem facade_prefix (env : Environment) (data : ByteArray) (value : U16)
    (position : Nat) (rest : Term) (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) :
    Result.ReadyPrefix (__APPEND__ ⟨3,7⟩ value) (decoded env 7 (appendInput data position rest))
      (.ok true) (returned env (appended (appendInput data position rest) value rest)) := by
  rw [facade_contract]
  have append := (append_prefix env data value position rest fits offset).bind
    (fun reply => do
      NativeOwnedDrop.drop (⟨3,7⟩ : NativeResourceArc shared_log.LogResource)
      match reply with
      | .Ok accepted => NativeM.ok accepted
      | .Err error => do NativeOwnedDrop.drop error; NativeM.ok false)
  have release := (release_prefix env (appended (appendInput data position rest) value rest)).bind
    (fun _ => NativeM.ok true)
  exact append.trans (by simpa only [Result.ok_bind, NativeM.ok] using release)

/-- Decoding, executing the actual compiled export and encoding its result all
compose with an arbitrary ordinary Elixir continuation. -/
theorem adapter_continuation {α : Type} (env : Environment) (data : ByteArray) (value : U16)
    (position : Nat) (rest : Term) (next : Term → Result α)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ env.nativeResourceTypes)
    (fits : data.size + 4 ≤ limit) (offset : position ≤ limit)
    (choices : List ScheduleChoice := []) :
    ((do
      let resource ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__APPEND__ resource value) Rustler.encodeBool) >>= next).run
      (pinned env (appendInput data position rest)) choices =
        (next Term.true).run (returned env (appended (appendInput data position rest) value rest)) choices := by
  have first := (decode_prefix env (appendInput data position rest) registered).bind
    (fun resource => Rustler.executeNative (__APPEND__ resource value) Rustler.encodeBool)
  have body := Rustler.executeNative_readyPrefix
    (facade_prefix env data value position rest fits offset) Rustler.encodeBool
  have trace := first.trans (by simpa only [Result.ok_bind, Rustler.encodeBool] using body)
  simpa [Rustler.encodeBool] using (trace.bind next).run choices

/-- An admitted existing resource and ready file actions. Constructor reachability
is a separate obligation; this initial state makes no constructor claim. -/
@[expose] def initial : Environment :=
  pinned ({ nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource]
            pdict := [(.atom "log", .nativeReference 6)] } : Environment)
    (appendInput ByteArray.empty 0 .nil)

/-- The existing-resource law can vary process-local fields and registration
without changing its admitted file and resource heap. -/
theorem initial_adapter {α : Type} (value : U16) (next : Term → Result α) (env : Environment)
    (counter : env.nativeRefCounter = 6) (heap : env.nativeHeap = initial.nativeHeap)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ env.nativeResourceTypes)
    (choices : List ScheduleChoice := []) :
    ((do
      let resource ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Rustler.executeNative (__APPEND__ resource value) Rustler.encodeBool
      next result) : Result α).run env choices =
      (next Term.true).run (returned env (appended (appendInput ByteArray.empty 0 .nil) value .nil)) choices := by
  have shape : pinned env (appendInput ByteArray.empty 0 .nil) = env := by
    cases env
    simp_all [pinned, framedEnv, initial]
  simpa only [shape, bind_assoc] using adapter_continuation env ByteArray.empty value 0 .nil next registered
    (by decide) (by decide) choices

end Record.NativeLogProperties
