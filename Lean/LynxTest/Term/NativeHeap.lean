module
import Lynx
meta import LynxTest.ProofAudit

namespace LynxTest.Term.NativeHeap
open Lynx

theorem consumes_unique_live (tag : String) (identity : Nat) (env : Environment)
    (nonzero : identity ≠ 0) (bounded : identity ≤ env.refCounter)
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
      {refCounter := 1,nativeHeap := [(1,"different",.atom "live")]} =
      (.error .exhausted,
        {refCounter := 1,nativeHeap := [(1,"different",.atom "live")]}) := by
  simp [Result.consumeNativeCapability]

theorem custom_payload :
    Result.consumeNativeCapability "expected" 1
      {refCounter := 1,nativeHeap := [(1,"expected",.atom "custom")]} =
      (.error .exhausted,
        {refCounter := 1,nativeHeap := [(1,"expected",.atom "custom")]}) := by
  simp [Result.consumeNativeCapability]

theorem duplicate_identity :
    Result.consumeNativeCapability "expected" 1
      {refCounter := 1,nativeHeap := [(1,"expected",.atom "live"),(1,"expected",.atom "live")]} =
      (.error .exhausted,
        {refCounter := 1,nativeHeap := [(1,"expected",.atom "live"),(1,"expected",.atom "live")]}) := by
  simp [Result.consumeNativeCapability]

theorem zero_identity (tag : String) (env : Environment) :
    Result.consumeNativeCapability tag 0 env = (.error .exhausted,env) := by
  simp [Result.consumeNativeCapability]

theorem unallocated_identity (tag : String) (env : Environment) :
    Result.consumeNativeCapability tag (env.refCounter + 1) env = (.error .exhausted,env) := by
  simp [Result.consumeNativeCapability]

end LynxTest.Term.NativeHeap
run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Term.NativeHeap
