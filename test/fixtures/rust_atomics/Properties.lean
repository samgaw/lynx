module
public import Atomic.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx atomic_analysis
namespace Atomic
abbrev Counter := NativeAtomic U64 (NativeAtomicStorage U64)

/-- Contract of the actual extracted callee, used across the crate boundary. -/
theorem claim_contract (counter : Counter) :
    atomic_core.claim counter = NativeAtomic.fetchAdd counter 1#u64 .SeqCst := by rfl

theorem claim_spec (counter : Counter) (value : U64) (env : Environment)
    (found : NativeAtomic.lookup counter env = some value) :
    atomic_core.claim counter env =
      (.ok value, NativeAtomic.update counter (NativeAtomic.wrappingAdd value 1#u64) env) := by
  simp [claim_contract, NativeAtomic.fetchAdd, found]

theorem current_spec (counter : Counter) (value : U64) (env : Environment)
    (found : NativeAtomic.lookup counter env = some value) :
    atomic_core.current counter env = (.ok value, env) := by
  simp [atomic_core.current, NativeAtomic.load, found]

theorem two_spec (counter : Counter) (value : U64) (env : Environment)
    (found : NativeAtomic.lookup counter env = some value)
    (updated : NativeAtomic.lookup counter
      (NativeAtomic.update counter (NativeAtomic.wrappingAdd value 1#u64) env) =
      some (NativeAtomic.wrappingAdd value 1#u64)) :
    claim_two counter env =
      (.ok (value, NativeAtomic.wrappingAdd value 1#u64),
        NativeAtomic.update counter
          (NativeAtomic.wrappingAdd (NativeAtomic.wrappingAdd value 1#u64) 1#u64)
          (NativeAtomic.update counter (NativeAtomic.wrappingAdd value 1#u64) env)) := by
  simp [claim_two, claim_contract, NativeAtomic.fetchAdd, found, updated, NativeM.ok]
theorem reset_spec (counter : Counter) (previous value : U64) (env : Environment)
    (found : NativeAtomic.lookup counter env = some previous) :
    atomic_core.reset counter value env = (.ok (), NativeAtomic.update counter value env) := by
  simp [atomic_core.reset, NativeAtomic.store, found, NativeM.ok]

theorem frame_unchanged (counter : Counter) (value : U64) (frame : List (Nat × String × Term))
    (absent : frame.any (fun cell => cell.1 == counter.id) = false) :
    frame.map (fun cell => if cell.1 = counter.id then
      (counter.id, NativeAtomic.typeName, NativeCodec.encode value) else cell) = frame := by
  induction frame with
  | nil => rfl
  | cons cell rest ih =>
    have absent' : cell.1 ≠ counter.id ∧ rest.any (fun cell => cell.1 == counter.id) = false := by
      simpa using absent
    simp [absent'.1, ih absent'.2]

theorem two_framed (counter : Counter) (value : U64) (env : Environment)
    (frame : List (Nat × String × Term))
    (heap : env.nativeHeap = (counter.id, NativeAtomic.typeName, NativeCodec.encode value) :: frame)
    (absent : frame.any (fun cell => cell.1 == counter.id) = false) :
    let next := NativeAtomic.wrappingAdd value 1#u64
    let after := NativeAtomic.wrappingAdd next 1#u64
    claim_two counter env =
      (.ok (value, next), {env with nativeHeap :=
        (counter.id, NativeAtomic.typeName, NativeCodec.encode after) :: frame}) := by
  have empty : frame.filter (fun cell => cell.1 == counter.id) = [] := by
    simpa only [List.filter_eq_nil_iff, List.any_eq_false] using absent
  have preserved (v : U64) := frame_unchanged counter v frame absent
  have found : NativeAtomic.lookup counter env = some value := by
    simp [NativeAtomic.lookup, heap, empty]
  have updated : NativeAtomic.lookup counter
      (NativeAtomic.update counter (NativeAtomic.wrappingAdd value 1#u64) env) =
      some (NativeAtomic.wrappingAdd value 1#u64) := by
    simp [NativeAtomic.lookup, NativeAtomic.update, heap, preserved, empty]
  simpa [NativeAtomic.update, heap, preserved] using two_spec counter value env found updated

@[expose] def initial : Environment :=
  {nativeRefCounter := 2, nativeHeap := [
    (1, NativeAtomic.typeName, NativeCodec.encode (18446744073709551615#u64)),
    (2,"foreign",.integer 42)]}

@[expose] def competing (claim : Counter → NativeM U64) : Result Term :=
  Result.schedule {} (do
    let ticket ← claim ⟨1⟩
    Result.send [] (.integer ticket.val) (.ok .nil)) fun _ => do
      let ticket ← claim ⟨1⟩
      Result.receive .infinity (fun _ message => some message) fun peer =>
        .nativeGet fun env =>
          match peer, NativeAtomic.lookup ⟨1⟩ env with
          | some (.integer other), some final =>
            .ok (if ((ticket.val == 0 && other == 18446744073709551615) ||
                (ticket.val == 18446744073709551615 && other == 0)) &&
                final.val == 1 && env.nativeHeap.length == 2 &&
                env.nativeHeap[1]? == some (2,"foreign",.integer 42) &&
                env.nativeRefCounter == 2 then Term.true else Term.false)
          | _,_ => .ok Term.false

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
attribute [local cbv_eval] Term.compare_atoms Term.compare_reference

theorem every_interleaving (elapsed : PID → Nat → Nat) :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 32
      (.start initial (competing atomic_core.claim) elapsed) = true := by cbv

theorem every_run : concurrentFrom initial (competing atomic_core.claim) (.ok Term.true) := by
  intro elapsed events last outcome run terminal
  have checked := Concurrent.check_sound (every_interleaving elapsed) run terminal
  split at checked
  · rfl
  · contradiction
end Atomic
