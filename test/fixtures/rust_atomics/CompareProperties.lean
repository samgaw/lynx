module
public import Atomic.Compare.Funs
public section
open Aeneas Aeneas.Std Lynx atomic_analysis
namespace Atomic.CompareProperties
theorem contract (counter : NativeAtomic U64 (NativeAtomicStorage U64)) (expected replacement : U64) :
    atomic_core.replace counter expected replacement =
      NativeAtomic.compareExchange counter expected replacement .SeqCst .SeqCst := by rfl


theorem matched (counter : NativeAtomic U64 (NativeAtomicStorage U64))
    (previous replacement : U64) (env : Environment)
    (found : NativeAtomic.lookup counter env = some previous) :
    atomic_core.replace counter previous replacement env =
      (.ok (.Ok previous), NativeAtomic.update counter replacement env) := by
  simp [contract, NativeAtomic.compareExchange, found]

theorem mismatch (counter : NativeAtomic U64 (NativeAtomicStorage U64))
    (previous expected replacement : U64) (env : Environment)
    (found : NativeAtomic.lookup counter env = some previous) (different : previous ≠ expected) :
    atomic_core.replace counter expected replacement env = (.ok (.Err previous),env) := by
  simp [contract, NativeAtomic.compareExchange, found, different]

theorem composed_match (counter : NativeAtomic U64 (NativeAtomicStorage U64))
    (previous replacement : U64) (env : Environment)
    (found : NativeAtomic.lookup counter env = some previous) :
    try_set counter previous replacement env =
      (.ok (true,previous), NativeAtomic.update counter replacement env) := by
  simp [try_set, contract, NativeAtomic.compareExchange, found, NativeM.ok]

theorem composed_mismatch (counter : NativeAtomic U64 (NativeAtomicStorage U64))
    (previous expected replacement : U64) (env : Environment)
    (found : NativeAtomic.lookup counter env = some previous) (different : previous ≠ expected) :
    try_set counter expected replacement env = (.ok (false,previous),env) := by
  simp [try_set, contract, NativeAtomic.compareExchange, found, different, NativeM.ok]


theorem unavailable (counter : NativeAtomic U64 (NativeAtomicStorage U64))
    (expected replacement : U64) (env : Environment)
    (missing : NativeAtomic.lookup counter env = none) :
    atomic_core.replace counter expected replacement env = (.error .exhausted,env) := by
  simp [contract, NativeAtomic.compareExchange, missing]

@[expose] def initial : Environment :=
  {nativeRefCounter := 2, nativeHeap := [
    (1,NativeAtomic.typeName,NativeCodec.encode (0#u64)), (2,"foreign",.integer 42)]}

@[expose] def competing
    (change : NativeAtomic U64 (NativeAtomicStorage U64) → U64 → U64 → NativeM (Bool × U64)) :
    Result Term :=
  Result.schedule {} (do
    let (success,observed) ← change ⟨1⟩ 0#u64 1#u64
    Result.send [] (.tuple #[if success then Term.true else Term.false, .integer observed.val]) (.ok .nil)) fun _ => do
      let (success,observed) ← change ⟨1⟩ 0#u64 2#u64
      Result.receive .infinity (fun _ message => some message) fun peer =>
        .nativeGet fun env =>
          match peer, NativeAtomic.lookup ⟨1⟩ env with
          | some (.tuple ⟨[.atom flag,.integer other]⟩), some final =>
            .ok (if ((success && observed.val == 0 && flag == "false" && other == 2 && final.val == 2) ||
                (!success && observed.val == 1 && flag == "true" && other == 0 && final.val == 1)) &&
                env.nativeHeap.length == 2 && env.nativeHeap[1]? == some (2,"foreign",.integer 42) &&
                env.nativeRefCounter == 2 then Term.true else Term.false)
          | _,_ => .ok Term.false

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
attribute [local cbv_eval] Term.compare_atoms Term.compare_reference

theorem every_interleaving (elapsed : PID → Nat → Nat) :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 32
      (.start initial (competing try_set) elapsed) = true := by cbv

theorem every_run : concurrentFrom initial (competing try_set) (.ok Term.true) := by
  intro elapsed events last outcome run terminal
  have checked := Concurrent.check_sound (every_interleaving elapsed) run terminal
  split at checked
  · rfl
  · contradiction
end Atomic.CompareProperties
