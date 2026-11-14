module
public import Record.GuardedRepairAdapter
public import Record.UnsyncedRepairLogProperties
public import Record.Extraction.RustlerAdapter
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.GuardedRepairTermAdapter
set_option maxRecDepth 8192
open NativeFile Record.Properties Record.ResizeProperties Record.LogProperties
  Record.RepairCrashProperties Record.CrashProperties Record.GuardedRepairAdapter

section
variable [admission : Admission]

/-- Correspondence with the actual generated compiled-export adapter, including
registration and cleanup after either scalar conversion fails. -/
theorem generated_adapter_safe_general (dispatcher : Dispatcher) (base : Environment)
    (poisoned : Bool) (before : State) (values : List U16) (maximum value : Term)
    (valid : Admitted before) (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Safe values)
      (Elixir.LynxIoFixture.Native.«log_repair_append/3» dispatcher (.nativeReference 6) maximum value)
      (pinned base poisoned before) := by
  rw [Elixir.LynxIoFixture.Native.«log_repair_append:adapter/3»]
  simpa [termBody, NativeResourceArc.typeName, NativeCodec.typeName] using
    term_adapter_safe base poisoned before values maximum value valid durable visible

theorem generated_adapter_safe (dispatcher : Dispatcher) (base : Environment)
    (poisoned : Bool) (before : State) (values : List U16) (maximum value : Term)
    (valid : Admitted before) (stable : before.durable = before.visible)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Safe values)
      (Elixir.LynxIoFixture.Native.«log_repair_append/3» dispatcher (.nativeReference 6) maximum value)
      (pinned base poisoned before) := by
  exact generated_adapter_safe_general dispatcher base poisoned before values maximum value valid (stable ▸ visible) visible

/-- All raw runtime prefixes retain the same byte/pin invariant, including
blocked scheduler entry without peers. This does not assert termination or
safety under interfering callers. -/
theorem generated_adapter_run_safe (dispatcher : Dispatcher) (base : Environment)
    (poisoned : Bool) (before : State) (values : List U16) (maximum value : Term)
    (valid : Admitted before) (stable : before.durable = before.visible)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event) (last : Concurrent.Config Term)
    (executed : Concurrent.Run (.start (pinned base poisoned before)
      (Elixir.LynxIoFixture.Native.«log_repair_append/3» dispatcher (.nativeReference 6) maximum value)
      elapsed) events last) :
    ∃ env, Safe values env ∧
      ((∃ residual, last = .start env residual elapsed) ∨
        ∃ residual, last = .running (Concurrent.State.initial env elapsed)
          [(env.currentPid, Concurrent.Task.root residual)] none false) := by
  exact (generated_adapter_safe dispatcher base poisoned before values maximum value valid stable visible).run elapsed executed

theorem generated_adapter_run_safe_general (dispatcher : Dispatcher) (base : Environment)
    (poisoned : Bool) (before : State) (values : List U16) (maximum value : Term)
    (valid : Admitted before) (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event) (last : Concurrent.Config Term)
    (executed : Concurrent.Run (.start (pinned base poisoned before)
      (Elixir.LynxIoFixture.Native.«log_repair_append/3» dispatcher (.nativeReference 6) maximum value)
      elapsed) events last) :
    ∃ env, Safe values env ∧
      ((∃ residual, last = .start env residual elapsed) ∨
        ∃ residual, last = .running (Concurrent.State.initial env elapsed)
          [(env.currentPid, Concurrent.Task.root residual)] none false) := by
  exact (generated_adapter_safe_general dispatcher base poisoned before values maximum value valid durable visible).run elapsed executed

/-- Exact successful returns of the compiled-export adapter supply the next
call's resource admission, including retained registration and error disposal. -/
theorem generated_adapter_returns (dispatcher : Dispatcher) (base : Environment)
    (poisoned : Bool) (before : State) (values : List U16) (maximum value result : Term)
    (valid : Admitted before) (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible) (world : Environment)
    (trace : Result.ReadyPrefix
      (Elixir.LynxIoFixture.Native.«log_repair_append/3» dispatcher (.nativeReference 6) maximum value)
      (pinned base poisoned before) (.ok result) world) :
    ∃ state consumed accepted, result = Rustler.encodeBool accepted ∧
      world = @pinned (nextAdmission consumed) (registeredBase base) poisoned state ∧ Admitted state ∧
      Prefix (disk (logBytes values)) state.visible ∧ Prefix (disk (logBytes values)) state.durable := by
  rw [Elixir.LynxIoFixture.Native.«log_repair_append:adapter/3»] at trace
  apply term_adapter_returns base poisoned before values maximum value result valid durable visible world
  simpa [termBody,NativeResourceArc.typeName,NativeCodec.typeName] using trace

/-- Ordinary sequential composition of actual generated NIF calls. A rejected
argument, panic or exhaustion stops the sequence through Result.bind. -/
@[expose] def calls (dispatcher : Dispatcher) : List (Term × Term) → Result Unit
  | [] => .ok ()
  | (maximum,value) :: rest => do
      let _ ← Elixir.LynxIoFixture.Native.«log_repair_append/3» dispatcher (.nativeReference 6) maximum value
      calls dispatcher rest

/-- All prefixes of any finite sequence preserve the acknowledged bytes in
both images and retain the independent VM owner. No per-call counter reset or
recreation of a consumed error is used in this induction. -/
theorem calls_safe (dispatcher : Dispatcher) (inputs : List (Term × Term)) (base : Environment)
    (poisoned : Bool) (before : State) (values : List U16) (valid : Admitted before)
    (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Safe values) (calls dispatcher inputs) (pinned base poisoned before) := by
  induction inputs generalizing admission base before with
  | nil =>
      exact .ok _ _ _ (generated_adapter_safe_general dispatcher base poisoned before values
        (.integer 0) (.integer 0) valid durable visible).initial
  | cons input rest ih =>
      rcases input with ⟨maximum,value⟩
      apply Result.NativeInvariant.bind
        (computation := Elixir.LynxIoFixture.Native.«log_repair_append/3» dispatcher (.nativeReference 6) maximum value)
        (generated_adapter_safe_general dispatcher base poisoned before values maximum value valid durable visible)
      intro result world trace
      obtain ⟨state,consumed,accepted,encoded,rfl,admitted,v,d⟩ :=
        generated_adapter_returns dispatcher base poisoned before values maximum value result valid durable visible world trace
      exact @ih (nextAdmission consumed) (registeredBase base) state admitted d v

end

/-- The general theorem applies to a concrete admitted unequal-image state for
all scalar terms, rather than relying on uninhabited input assumptions. -/
theorem unsynced_initial_safe (dispatcher : Dispatcher) (maximum value : Term) :
    Result.NativeInvariant (Safe [13#u16])
      (Elixir.LynxIoFixture.Native.«log_repair_append/3» dispatcher (.nativeReference 6) maximum value)
      Record.UnsyncedRepairLogProperties.initial := by
  exact generated_adapter_safe_general dispatcher
    ({pdict := [(.atom "log",.nativeReference 6)]} : Environment) false
    Record.UnsyncedRepairLogProperties.initialState [13#u16] maximum value
    Record.UnsyncedRepairLogProperties.initial_admitted
    Record.UnsyncedRepairLogProperties.initial_durable_prefix
    Record.UnsyncedRepairLogProperties.initial_visible_prefix

/-- The sequence theorem also has inhabited admissions after earlier allocations
and after the reusable error capability has been consumed. -/
@[expose, instance_reducible] def laterAdmission : Admission := ⟨42,by decide,false⟩
@[expose] def laterState : State :=
  ⟨Record.RepairingLogProperties.torn,Record.RepairingLogProperties.torn,0,
    Record.RepairingLogProperties.fileScript⟩
@[expose] def laterInitial : Environment := @pinned laterAdmission
  ({pdict := [(.atom "log",.nativeReference 6)]} : Environment) false laterState

theorem later_calls_safe (dispatcher : Dispatcher) (inputs : List (Term × Term)) :
    Result.NativeInvariant (Safe [13#u16]) (calls dispatcher inputs) laterInitial := by
  apply @calls_safe laterAdmission dispatcher inputs _ false laterState [13#u16]
  · unfold Admitted; decide
  all_goals change Prefix (disk (logBytes [13#u16])) (disk (logBytes [13#u16] ++ [7#u8]))
  all_goals exact Record.RepairCrashProperties.prefix_append _ _

@[expose] def laterAccepted (config : Concurrent.Config Unit) : Bool :=
  match config.outcome with
  | .ok () =>
      let env := Record.RepairingLogProperties.snapshot config
      Record.RepairingLogProperties.stateAccepted Record.RepairingLogProperties.complete 46 env &&
        !env.nativeHeap.any (fun cell => 7 ≤ cell.1)
  | _ => false

set_option maxHeartbeats 16000000 in
set_option cbv.maxSteps 32000000 in
/-- A non-vacuous actual two-call execution returns with the exact advanced
counter and no temporary owners, leases or recreated error capability. -/
theorem later_calls_checked (dispatcher : Dispatcher) :
    Concurrent.checkPost laterAccepted 768 (.start laterInitial
      (calls dispatcher [(.integer 4,.integer 19),(.integer 4,.integer 23)])
      (fun _ _ => 0)) = true := by
  cbv

end Record.GuardedRepairTermAdapter
