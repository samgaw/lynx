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

end Record.GuardedRepairTermAdapter
