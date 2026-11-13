module
import Lynx
meta import LynxTest.ProofAudit

namespace LynxTest.Term.NativeHeap
open Lynx

theorem consumes_unique_live (tag : String) (identity : Nat) (env : Environment)
    (nonzero : identity ≠ 0) (bounded : identity ≤ env.nativeRefCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == identity) =
      [(identity,tag,.atom "live")]) :
    Result.consumeNativeCapability tag identity env =
      (.ok (), {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != identity)}) := by
  simp [Result.consumeNativeCapability,nonzero,Nat.not_lt_of_ge bounded,stored]

theorem missing_rejected (tag : String) (identity : Nat) (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == identity) = []) :
    Result.consumeNativeCapability tag identity env = (.error .exhausted,env) := by
  simp [Result.consumeNativeCapability,missing]

theorem repeated_rejected (tag : String) (identity : Nat) (env : Environment) :
    Result.consumeNativeCapability tag identity
      {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != identity)} =
      (.error .exhausted,
        {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != identity)}) := by
  apply missing_rejected
  simp [List.filter_filter]

theorem wrong_type :
    Result.consumeNativeCapability "expected" 1
      {nativeRefCounter := 1,nativeHeap := [(1,"different",.atom "live")]} =
      (.error .exhausted,
        {nativeRefCounter := 1,nativeHeap := [(1,"different",.atom "live")]}) := by
  simp [Result.consumeNativeCapability]

theorem custom_payload :
    Result.consumeNativeCapability "expected" 1
      {nativeRefCounter := 1,nativeHeap := [(1,"expected",.atom "custom")]} =
      (.error .exhausted,
        {nativeRefCounter := 1,nativeHeap := [(1,"expected",.atom "custom")]}) := by
  simp [Result.consumeNativeCapability]

theorem duplicate_identity :
    Result.consumeNativeCapability "expected" 1
      {nativeRefCounter := 1,nativeHeap := [(1,"expected",.atom "live"),(1,"expected",.atom "live")]} =
      (.error .exhausted,
        {nativeRefCounter := 1,nativeHeap := [(1,"expected",.atom "live"),(1,"expected",.atom "live")]}) := by
  simp [Result.consumeNativeCapability]

theorem zero_identity (tag : String) (env : Environment) :
    Result.consumeNativeCapability tag 0 env = (.error .exhausted,env) := by
  simp [Result.consumeNativeCapability]

theorem unallocated_identity (tag : String) (env : Environment) :
    Result.consumeNativeCapability tag (env.nativeRefCounter + 1) env = (.error .exhausted,env) := by
  simp [Result.consumeNativeCapability]

theorem explicit_initial_state :
    concurrentFrom {nativeRefCounter := 7}
      (Result.nativeGet fun env => .ok env.nativeRefCounter) (.ok 7) := by
  intro elapsed events last result run terminal
  have trace : Result.ReadyPrefix (.nativeGet fun env => .ok env.nativeRefCounter)
      {nativeRefCounter := 7} (.ok 7) {nativeRefCounter := 7} :=
    .nativeGet _ _ _ _ (.refl _ _)
  exact trace.returns elapsed run terminal

theorem scheduler_choices_remain_universal (initial : Environment) :
    concurrentFrom initial (Result.nativeGet fun env => .ok (env.nativeRefCounter, env.nativeHeap))
      (.ok (initial.nativeRefCounter, initial.nativeHeap)) := by
  intro elapsed events last result run terminal
  have trace : Result.ReadyPrefix (.nativeGet fun env => .ok (env.nativeRefCounter, env.nativeHeap))
      initial (.ok (initial.nativeRefCounter, initial.nativeHeap)) initial :=
    .nativeGet _ _ _ _ (.refl _ _)
  exact trace.returns elapsed run terminal

theorem fresh_runtime_unchanged (computation : Result α) (outcome : Outcome α) :
    concurrentFrom {} computation outcome ↔ concurrent computation outcome := Iff.rfl

theorem admitted_cleanup_from_context :
    concurrentFrom {nativeRefCounter := 1,nativeHeap := [(1,"expected",.atom "live")]}
      (Result.consumeNativeCapability "expected" 1) (.ok ()) := by
  intro elapsed events last result run terminal
  have trace : Result.ReadyPrefix (Result.consumeNativeCapability "expected" 1)
      {nativeRefCounter := 1,nativeHeap := [(1,"expected",.atom "live")]}
      (.ok ()) {nativeRefCounter := 1} := by
    refine .wait _ _ (Except.ok ()) _ _ _ _ ?_ (.refl _ _)
    rfl
  exact trace.returns elapsed run terminal

private def sharedCleanup : Result :=
  .nativeSet {nativeRefCounter := 1, nativeHeap := [(1,"expected",.atom "live")]} <|
    Result.schedule {} (do
      Result.consumeNativeCapability "expected" 1
      Result.ok .nil) fun _ =>
        .wait (fun env => if env.nativeHeap.isEmpty then some ((), env) else none) fun _ =>
          .nativeGet fun env => .ok (.integer env.nativeRefCounter)

/-- Capability cleanup in a child uses the shared allocator and is visible to
its waiting parent under every finite scheduler choice list. -/
theorem scheduled_cleanup :
    concurrent sharedCleanup (.ok (.integer 1)) := by
  refine concurrent_of_check sharedCleanup
    (fun | .ok (.integer 1) => true | _ => false) 24 (by intro elapsed; cbv) ?_
  intro result accepted
  split at accepted
  · rfl
  · contradiction

private def competingCleanup : Result :=
  Result.schedule {} (do
    Result.consumeNativeCapability "expected" 1
    .ok .nil) fun _ => do
      Result.consumeNativeCapability "expected" 1
      .ok .nil

/-- Sharing one ownership token between workers cannot certify two successful
consumptions, regardless of the transition order. -/
theorem concurrent_double_consumption_rejected (elapsed : PID → Nat → Nat) :
    Concurrent.check (fun | .error .exhausted => true | _ => false) 24
      (.start {nativeRefCounter := 1, nativeHeap := [(1,"expected",.atom "live")]}
        competingCleanup elapsed) = true := by
  cbv

end LynxTest.Term.NativeHeap
run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Term.NativeHeap
