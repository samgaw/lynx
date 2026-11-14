module
public import Record.GuardedRepairAdapter
public import Record.Extraction.RustlerAdapter
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.GuardedRepairTermAdapter
set_option maxRecDepth 8192
open NativeFile Record.Properties Record.ResizeProperties Record.LogProperties
  Record.RepairCrashProperties Record.CrashProperties Record.GuardedRepairAdapter

/-- Correspondence with the actual generated compiled-export adapter, including
registration and cleanup after either scalar conversion fails. -/
theorem generated_adapter_safe (dispatcher : Dispatcher) (base : Environment)
    (poisoned : Bool) (before : State) (values : List U16) (maximum value : Term)
    (valid : Admitted before) (stable : before.durable = before.visible)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Safe values)
      (Elixir.LynxIoFixture.Native.«log_repair_append/3» dispatcher (.nativeReference 6) maximum value)
      (pinned base poisoned before) := by
  rw [Elixir.LynxIoFixture.Native.«log_repair_append:adapter/3»]
  simpa [termBody, NativeResourceArc.typeName, NativeCodec.typeName] using
    term_adapter_safe base poisoned before values maximum value valid stable visible

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

end Record.GuardedRepairTermAdapter
