module
public import Atomic.Resource.Funs
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Atomic.ResourceProperties
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

/-- The extracted first-party primitive remains the cross-crate contract. -/
theorem claim_contract (counter : NativeAtomic U64 (NativeAtomicStorage U64)) :
    atomic_core.claim counter = NativeAtomic.fetchAdd counter 1#u64 .SeqCst := by rfl

theorem pair_contract (counter : NativeAtomic U64 (NativeAtomicStorage U64)) :
    atomic_analysis.claim_two counter = (do
      let first ← NativeAtomic.fetchAdd counter 1#u64 .SeqCst
      let second ← NativeAtomic.fetchAdd counter 1#u64 .SeqCst
      NativeM.ok (first, second)) := by
  simp [atomic_analysis.claim_two, claim_contract]

theorem reference_eq (left right : Nat) :
    (Term.nativeReference left == Term.nativeReference right) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  rw [Term.beq_iff_compare_eq, Term.compare_eq_reference]
  simp

@[expose] def initial : Environment :=
  {nativeResourceTypes := [NativeResourceArc.typeName Counter]}

/-- Constructing an actual atomic resource, composing two calls across crates
and consuming its last owner retires the resource, owner and nested atomic cell. -/
theorem cycle (value : U64) (schedule : List ScheduleChoice) :
    (counter_cycle value).run initial schedule =
      (.ok (.Ok (value, NativeAtomic.wrappingAdd value 1#u64)),
        {initial with nativeRefCounter := 3}) := by
  simp [counter_cycle, counter_new, counter_pair, pair_contract, initial,
    NativeResourceArc.newManagedCaptured, NativeResourceArc.newOwned, NativeResourceArc.new,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.new, NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.fetchAdd, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeResourceUnwindDrop.drop, NativeOwnedDrop.drop, NativeM.allocate, NativeM.removeCell,
    NativeM.capturePanic, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq,
    Result.handle, Result.bind, Result.ofExcept]

/-- An unregistered resource allocation panics and retires the nested cell. -/
theorem unregistered (value : U64) (schedule : List ScheduleChoice) :
    (counter_cycle value).run {} schedule = (.ok (.Err ()), {nativeRefCounter := 1}) := by
  simp [counter_cycle, counter_new, counter_pair, pair_contract, initial,
    NativeResourceArc.newManagedCaptured, NativeResourceArc.newOwned, NativeResourceArc.new,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.new, NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.fetchAdd, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeResourceUnwindDrop.drop, NativeOwnedDrop.drop, NativeM.allocate, NativeM.removeCell,
    NativeM.capturePanic, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq,
    Result.handle, Result.bind, Result.ofExcept]

/-- A rejected request executes its actual compiler cleanup before the captured
panic result. No owner or nested atomic cell survives. -/
theorem rejected (value : U64) (schedule : List ScheduleChoice) :
    (counter_checked value false).run initial schedule =
      (.ok (.Err ()), {initial with nativeRefCounter := 3}) := by
  simp [counter_checked, counter_new, counter_pair, pair_contract, initial,
    NativeResourceArc.newManagedCaptured, NativeResourceArc.newOwned, NativeResourceArc.new,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.new, NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.fetchAdd, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeResourceUnwindDrop.drop, NativeOwnedDrop.drop, NativeM.allocate, NativeM.removeCell,
    NativeM.capturePanic, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq,
    Result.handle, Result.bind, Result.ofExcept]

/-- Accepted requests return the exact tuple after both cross-crate updates. -/
theorem accepted (value : U64) (schedule : List ScheduleChoice) :
    (counter_checked value true).run initial schedule =
      (.ok (.Ok (value, NativeAtomic.wrappingAdd value 1#u64)),
        {initial with nativeRefCounter := 3}) := by
  simp [counter_checked, counter_new, counter_pair, pair_contract, initial,
    NativeResourceArc.newManagedCaptured, NativeResourceArc.newOwned, NativeResourceArc.new,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.new, NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.fetchAdd, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeResourceUnwindDrop.drop, NativeOwnedDrop.drop, NativeM.allocate, NativeM.removeCell,
    NativeM.capturePanic, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq,
    Result.handle, Result.bind, Result.ofExcept]

/-- Logical resource retirement preserves an arbitrary foreign cell's contents. -/
theorem cycle_foreign (value : U64) (foreign : Term) (schedule : List ScheduleChoice) :
    (counter_cycle value).run {initial with nativeRefCounter := 99, nativeHeap := [(99,"foreign",foreign)]} schedule =
      (.ok (.Ok (value, NativeAtomic.wrappingAdd value 1#u64)),
        {initial with nativeRefCounter := 102, nativeHeap := [(99,"foreign",foreign)]}) := by
  simp [counter_cycle, counter_new, counter_pair, pair_contract, initial,
    NativeResourceArc.newManagedCaptured, NativeResourceArc.newOwned, NativeResourceArc.new,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.new, NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.fetchAdd, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeResourceUnwindDrop.drop, NativeOwnedDrop.drop, NativeM.allocate, NativeM.removeCell,
    NativeM.capturePanic, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq,
    Result.handle, Result.bind, Result.ofExcept]
end Atomic.ResourceProperties
