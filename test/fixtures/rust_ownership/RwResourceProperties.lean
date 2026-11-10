module
public import RwShared.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace RwShared.Properties

theorem reference_eq (left right : Nat) :
    (Term.nativeReference left == Term.nativeReference right) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  rw [Term.beq_iff_compare_eq, Term.compare_eq_reference]
  simp

theorem toggle_base (value : Bool) : ownership_base.toggle value = NativeM.ok (!value) := by
  cases value <;> rfl

theorem toggle_app (value : Bool) : ownership_app.toggle value = NativeM.ok (!value) := by
  simp [ownership_app.toggle, toggle_base, NativeM.ok]

@[expose] def initial : Environment :=
  {nativeResourceTypes := [NativeResourceArc.typeName RwResource]}

set_option maxHeartbeats 1000000 in
theorem shared_cycle (value : Bool) (schedule : List ScheduleChoice) :
    (rw_resource_cycle value).run initial schedule =
      (.ok (.Ok (!value)), {initial with nativeRefCounter := 6}) := by
  cases value <;>
    simp [rw_resource_cycle, rw_resource_new, rw_resource_toggle, toggle_app, initial,
      NativeResourceArc.newManagedCaptured, NativeResourceArc.newOwned, NativeResourceArc.new,
      NativeResourceArc.clone, NativeResourceArc.deref, NativeResourceArc.releaseOwned,
      NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
      NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
      NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
      NativeRwLock.new, NativeRwLock.read, NativeRwLock.write,
      NativeRwLock.acquireRead, NativeRwLock.acquireWrite,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwLock.state, NativeRwLock.store, NativeRwLock.contents, NativeRwLock.decodeState,
      NativeRwLock.decodeLease, NativeRwLock.lease, NativeRwLock.readerLimit,
      NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut, NativePoisonError.into_inner,
      NativeOwnedDrop.drop, NativeM.allocate, NativeM.removeCell, NativeM.capturePanic,
      NativeM.ok, NativeM.fail, NativeM.lift, NativeCodec.encode, NativeCodec.decode, NativeCodec.typeName,
      NativeRwLock.typeName, reference_eq, List.eraseDups_cons, List.eraseDups_nil,
      Result.handle, Result.bind, Result.ofExcept]
set_option maxHeartbeats 1000000 in
theorem unregistered (value : Bool) (schedule : List ScheduleChoice) :
    (rw_resource_cycle value).run {} schedule =
      (.ok (.Err ()), {nativeRefCounter := 1}) := by
  cases value <;>
    simp [rw_resource_cycle, rw_resource_new, rw_resource_toggle, toggle_app, initial,
      NativeResourceArc.newManagedCaptured, NativeResourceArc.newOwned, NativeResourceArc.new,
      NativeResourceArc.clone, NativeResourceArc.deref, NativeResourceArc.releaseOwned,
      NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
      NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
      NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
      NativeRwLock.new, NativeRwLock.read, NativeRwLock.write,
      NativeRwLock.acquireRead, NativeRwLock.acquireWrite,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwLock.state, NativeRwLock.store, NativeRwLock.contents, NativeRwLock.decodeState,
      NativeRwLock.decodeLease, NativeRwLock.lease, NativeRwLock.readerLimit,
      NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut, NativePoisonError.into_inner,
      NativeOwnedDrop.drop, NativeM.allocate, NativeM.removeCell, NativeM.capturePanic,
      NativeM.ok, NativeM.fail, NativeM.lift, NativeCodec.encode, NativeCodec.decode, NativeCodec.typeName,
      NativeRwLock.typeName, reference_eq, List.eraseDups_cons, List.eraseDups_nil,
      Result.handle, Result.bind, Result.ofExcept]

set_option maxHeartbeats 1000000 in
theorem reject_registered (value accepted : Bool) (schedule : List ScheduleChoice) :
    (rw_resource_reject value accepted).run initial schedule =
      (.ok (if accepted then .Ok (!value) else .Err ()),
       {initial with nativeRefCounter := if accepted then 6 else 3}) := by
  cases accepted <;> cases value <;>
    simp [rw_resource_reject, NativeResourceUnwindDrop.drop, rw_resource_cycle, rw_resource_new, rw_resource_toggle, toggle_app, initial,
      NativeResourceArc.newManagedCaptured, NativeResourceArc.newOwned, NativeResourceArc.new,
      NativeResourceArc.clone, NativeResourceArc.deref, NativeResourceArc.releaseOwned,
      NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
      NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
      NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
      NativeRwLock.new, NativeRwLock.read, NativeRwLock.write,
      NativeRwLock.acquireRead, NativeRwLock.acquireWrite,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwLock.state, NativeRwLock.store, NativeRwLock.contents, NativeRwLock.decodeState,
      NativeRwLock.decodeLease, NativeRwLock.lease, NativeRwLock.readerLimit,
      NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut, NativePoisonError.into_inner,
      NativeOwnedDrop.drop, NativeM.allocate, NativeM.removeCell, NativeM.capturePanic,
      NativeM.ok, NativeM.fail, NativeM.lift, NativeCodec.encode, NativeCodec.decode, NativeCodec.typeName,
      NativeRwLock.typeName, reference_eq, List.eraseDups_cons, List.eraseDups_nil,
      Result.handle, Result.bind, Result.ofExcept]

end RwShared.Properties
