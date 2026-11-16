module
public import GuardedRecovery.AdapterProof
public import GuardedRecovery.RecoveryTrace
public import GuardedRecovery.RecoveryCompleteness
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedRecovery.RecoveryAdapter
open GuardedRecovery.RecoveryTrace

@[expose] def encode : Reply → Term :=
  Rustler.encodeResult (fun value => .tuple #[
    Rustler.encodeOption Rustler.encodeUnsigned value.1,
    Rustler.encodeOption Rustler.encodeUnsigned value.2]) Rustler.encodeUnsigned

set_option maxRecDepth 16384 in
/-- The actual compiled export, generated adapter and extracted facade agree on
registration, execution and return encoding. No native function is substituted. -/
theorem recovery_contract : AdapterProof.recovery =
    Rustler.withResourceTypes NifProperties.registered
      (Rustler.executeNative (reopen_words path) encode) := by
  rfl

/-- Checked Rust recovery traces survive the actual adapter's registration,
panic conversion and encoding, with their full final environments retained. -/
theorem recovery_ready {before after : Environment} {value : Reply}
    (trace : Reopens path {before with nativeResourceTypes :=
      (before.nativeResourceTypes ++ NifProperties.registered).eraseDups} value after) :
    Result.ReadyPrefix AdapterProof.recovery before (.ok (encode value)) after := by
  rw [recovery_contract]
  apply Rustler.withResourceTypes_readyPrefix
  simpa only [Rustler.executeNative_ok] using Rustler.executeNative_readyPrefix trace.ready encode

/-- Every successful return of the actual generated adapter originates in a
completed extracted recovery trace, after actual resource registration. -/
theorem recovery_complete {before after : Environment} {encoded : Term}
    (trace : Result.ReadyPrefix AdapterProof.recovery before (.ok encoded) after) :
    ∃ value, encoded = encode value ∧ Reopens path
      {before with nativeResourceTypes := (before.nativeResourceTypes ++ NifProperties.registered).eraseDups}
      value after := by
  rw [recovery_contract] at trace
  have computation := Rustler.withResourceTypes_returns NifProperties.registered trace
  obtain ⟨value,encoding,returned⟩ := Rustler.executeNative_returns computation
  exact ⟨value,encoding,GuardedRecovery.RecoveryCompleteness.reopen_complete returned⟩

/-- The modelled boundary and extracted Rust recovery have precisely the same
successful encoded executions, with the full final environment preserved. -/
theorem recovery_iff (before after : Environment) (encoded : Term) :
    Result.ReadyPrefix AdapterProof.recovery before (.ok encoded) after ↔
      ∃ value, encoded = encode value ∧ Reopens path
        {before with nativeResourceTypes := (before.nativeResourceTypes ++ NifProperties.registered).eraseDups}
        value after := by
  constructor
  · exact recovery_complete
  · rintro ⟨value,rfl,trace⟩
    exact recovery_ready trace

/-- Every witnessed fault/data scenario works with any incoming loader registry.
The final state includes the actual deduplicated registration and Rust cleanup. -/
theorem admitted_adapter (available : List String) (counter : Nat) (scenario : Scenario)
    (positive : 2 ≤ counter) :
    Result.ReadyPrefix AdapterProof.recovery (initial available counter scenario)
      (.ok (encode (output scenario)))
      (finalState (available ++ NifProperties.registered).eraseDups counter scenario) := by
  apply recovery_ready
  simpa only [initial] using
    admitted_recovery (available ++ NifProperties.registered).eraseDups counter scenario positive

/-- Adapter execution has the exact result and state established by Rust recovery;
no successful return can be supplied by panic conversion. -/
theorem admitted_every_run (available : List String) (counter : Nat) (scenario : Scenario)
    (positive : 2 ≤ counter) (elapsed : PID → Nat → Nat)
    (run : Concurrent.Run (.start (initial available counter scenario) AdapterProof.recovery elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) :
    last = .start (finalState (available ++ NifProperties.registered).eraseDups counter scenario)
      (.ok (encode (output scenario))) elapsed ∧ outcome = .ok (encode (output scenario)) := by
  obtain ⟨rest,executed⟩ := (admitted_adapter available counter scenario positive).terminalRun elapsed run terminal
  cases executed with
  | refl => exact ⟨rfl,terminal.outcome_eq.symm⟩
  | step step _ =>
    simp [Concurrent.Step,Concurrent.Config.successors,Concurrent.isRequest] at step

end GuardedRecovery.RecoveryAdapter
