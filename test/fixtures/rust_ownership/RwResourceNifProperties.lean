module
public import RwShared.Properties
public import RwShared.RustlerBridge
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace RwShared.Properties

theorem facade_new (value : Bool) : __NEW__ value = rw_resource_new value := by
  have propagate (result : core.result.Result (NativeResourceArc RwResource) Unit) :
      (match result with
        | .Ok _ => Result.ok result
        | .Err _ => Result.ok (.Err ())) = Result.ok result := by
    cases result with
    | Ok value => rfl
    | Err error => cases error; rfl
  unfold __NEW__
  change (rw_resource_new value >>= fun result =>
    match result with | .Ok _ => Result.ok result | .Err _ => Result.ok (.Err ())) = _
  rw [funext propagate]
  simp

theorem facade_toggle (owner : NativeResourceArc RwResource) :
    __TOGGLE__ owner = rw_resource_toggle owner := by simp [__TOGGLE__]

theorem facade_read (owner : NativeResourceArc RwResource) :
    __READ__ owner = rw_resource_read owner := by simp [__READ__]

theorem facade_checked (value accepted : Bool) :
    __CHECKED__ value accepted = rw_resource_reject value accepted := by
  have propagate (result : core.result.Result Bool Unit) :
      (match result with
        | .Ok _ => Result.ok result
        | .Err _ => Result.ok (.Err ())) = Result.ok result := by
    cases result with
    | Ok value => rfl
    | Err error => cases error; rfl
  unfold __CHECKED__
  change (rw_resource_reject value accepted >>= fun result =>
    match result with | .Ok _ => Result.ok result | .Err _ => Result.ok (.Err ())) = _
  rw [funext propagate]
  simp

@[expose] def pinned (value : Bool) (counter : Nat) : Environment :=
  {initial with nativeRefCounter := counter, nativeHeap :=
    NativeResourceArc.vmCells ({state := ⟨1⟩} : RwResource) 2 4 5 ++
      [(1, NativeRwLock.typeName Bool,
        NativeRwLock.contents (⟨[],none,false,value⟩ : NativeRwLock.State Bool))]}

set_option maxHeartbeats 1000000 in
theorem factory_next {β : Type} (value : Bool) (next : Term → Result β)
    (schedule : List ScheduleChoice) :
    (do
      let term ← Rustler.executeNative (do
        let owner ← NativeM.resumeCaptured (__NEW__ value)
        let term ← NativeResourceArc.encode owner
        NativeOwnedDrop.drop owner
        Result.ok term) id
      next term).run initial schedule =
        (next (.nativeReference 5)).run (pinned value 5) schedule := by
  cases value <;>
    simp [facade_new, rw_resource_new, pinned, initial, NativeRwLock.new,
      NativeResourceArc.newManagedCaptured, NativeResourceArc.newOwned, NativeResourceArc.new,
      NativeResourceArc.encode_eq, NativeResourceArc.clone, NativeResourceArc.releaseOwned,
      NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
      NativeResourceArc.retiredState, NativeResourceArc.vmCells, NativeResourceArc.termType, NativeResourceArc.typeName,
      NativeResourceArc.handleType, NativeResourceArc.referenceLimit,
      NativeResourceCleanup.observable, NativeOwnedDrop.drop, Rustler.executeNative,
      NativeM.resumeCaptured, NativeM.capturePanic, NativeM.allocate, NativeM.ok,
      NativeCodec.encode, NativeCodec.decode, NativeCodec.typeName, NativeRwLock.typeName,
      NativeRwLock.contents, reference_eq, List.eraseDups_cons, List.eraseDups_nil,
      Result.wait_run, Result.handle, Result.bind, Result.ofExcept]
set_option maxHeartbeats 1000000 in
theorem toggle_next {β : Type} (value : Bool) (counter : Nat) (bounded : 5 ≤ counter)
    (next : Term → Result β) (schedule : List ScheduleChoice) :
    (do
      let owner ← NativeResourceArc.decode (α := RwResource) (.nativeReference 5)
      let term ← Rustler.executeNative (__TOGGLE__ owner) Rustler.encodeBool
      next term).run (pinned value counter) schedule =
        (next (Rustler.encodeBool (!value))).run (pinned (!value) (counter + 4)) schedule := by
  have small0 : counter ≠ 0 := by omega
  have small1 : counter ≠ 1 := by omega
  have small2 : counter ≠ 2 := by omega
  have small3 : counter ≠ 3 := by omega
  have small4 : counter ≠ 4 := by omega
  cases value <;>
    simp [small0, small1, small2, small3, small4, rw_resource_toggle, rw_resource_read, toggle_app, initial,
            NativeResourceArc.clone, NativeResourceArc.deref, NativeResourceArc.releaseOwned,
      NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
      NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
      NativeResourceArc.referenceLimit,       NativeRwLock.read, NativeRwLock.pollRead, NativeRwLock.pollWrite, NativeRwLock.prepareWrite,
      NativeRwLock.writerWaiting, NativeRwLock.writerRequestType, NativeRwLock.write,
      NativeRwLock.acquireRead, NativeRwLock.acquireWrite,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwLock.state, NativeRwLock.store, NativeRwLock.contents, NativeRwLock.decodeState,
      NativeRwLock.decodeLease, NativeRwLock.lease, NativeRwLock.readerLimit,
      NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut, NativePoisonError.into_inner,
      NativeOwnedDrop.drop, NativeM.removeCell,       NativeM.ok, NativeM.lift, NativeCodec.roundtrip, NativeCodec.typeName,
      NativeRwLock.typeName, reference_eq, List.eraseDups_cons, List.eraseDups_nil,
      Result.wait_run, Result.handle, Result.ofExcept, NativeResourceArc.decode_eq, NativeResourceArc.termType, NativeResourceArc.vmCells,
      facade_toggle, facade_read, Rustler.executeNative, pinned, Nat.add_assoc]

set_option maxHeartbeats 1000000 in
theorem read_next {β : Type} (value : Bool) (counter : Nat) (bounded : 5 ≤ counter)
    (next : Term → Result β) (schedule : List ScheduleChoice) :
    (do
      let owner ← NativeResourceArc.decode (α := RwResource) (.nativeReference 5)
      let term ← Rustler.executeNative (__READ__ owner) Rustler.encodeBool
      next term).run (pinned value counter) schedule =
        (next (Rustler.encodeBool (value))).run (pinned (value) (counter + 2)) schedule := by
  have small0 : counter ≠ 0 := by omega
  have small1 : counter ≠ 1 := by omega
  have small2 : counter ≠ 2 := by omega
  have small3 : counter ≠ 3 := by omega
  have small4 : counter ≠ 4 := by omega
  cases value <;>
    simp [small0, small1, small2, small3, small4, rw_resource_read, initial,
            NativeResourceArc.clone, NativeResourceArc.deref, NativeResourceArc.releaseOwned,
      NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
      NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
      NativeResourceArc.referenceLimit,       NativeRwLock.read, NativeRwLock.pollRead, NativeRwLock.pollWrite, NativeRwLock.prepareWrite,
      NativeRwLock.writerWaiting, NativeRwLock.writerRequestType,       NativeRwLock.acquireRead,       NativeRwLock.releaseRead, NativeRwLock.dispose,
      NativeRwLock.state, NativeRwLock.store, NativeRwLock.contents, NativeRwLock.decodeState,
      NativeRwLock.decodeLease, NativeRwLock.lease, NativeRwLock.readerLimit,
      NativeRwReadGuard.deref, NativePoisonError.into_inner,
      NativeOwnedDrop.drop, NativeM.removeCell,       NativeM.ok, NativeCodec.roundtrip, NativeCodec.typeName,
      NativeRwLock.typeName, reference_eq, List.eraseDups_cons, List.eraseDups_nil,
      Result.wait_run, Result.handle, Result.ofExcept, NativeResourceArc.decode_eq, NativeResourceArc.termType, NativeResourceArc.vmCells,
      facade_read, Rustler.executeNative, pinned, Nat.add_assoc]

set_option maxHeartbeats 1000000 in
theorem checked_next {β : Type} (value accepted : Bool) (next : Term → Result β)
    (schedule : List ScheduleChoice) :
    (do
      let term ← Rustler.executeNative (NativeM.resumeCaptured (__CHECKED__ value accepted)) Rustler.encodeBool
      next term).run initial schedule =
        if accepted then (next (Rustler.encodeBool (!value))).run {initial with nativeRefCounter := 6} schedule
        else (.error (.error (.atom "nif_panicked")), {initial with nativeRefCounter := 3}) := by
  cases accepted <;> cases value <;>
    simp [facade_checked, Rustler.executeNative, NativeM.resumeCaptured, rw_resource_reject, NativeResourceUnwindDrop.drop, rw_resource_cycle, rw_resource_new, rw_resource_toggle, toggle_app, initial,
      NativeResourceArc.newManagedCaptured, NativeResourceArc.newOwned, NativeResourceArc.new,
      NativeResourceArc.clone, NativeResourceArc.deref, NativeResourceArc.releaseOwned,
      NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
      NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
      NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
      NativeRwLock.new, NativeRwLock.read, NativeRwLock.pollRead, NativeRwLock.pollWrite, NativeRwLock.prepareWrite,
      NativeRwLock.writerWaiting, NativeRwLock.writerRequestType, NativeRwLock.write,
      NativeRwLock.acquireRead, NativeRwLock.acquireWrite,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwLock.state, NativeRwLock.store, NativeRwLock.contents, NativeRwLock.decodeState,
      NativeRwLock.decodeLease, NativeRwLock.lease, NativeRwLock.readerLimit,
      NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut, NativePoisonError.into_inner,
      NativeOwnedDrop.drop, NativeM.allocate, NativeM.removeCell, NativeM.capturePanic,
      NativeM.ok, NativeM.fail, NativeM.lift, NativeCodec.encode, NativeCodec.decode, NativeCodec.typeName,
      NativeRwLock.typeName, reference_eq, List.eraseDups_cons, List.eraseDups_nil,
      Result.wait_run, Result.handle, Result.bind, Result.ofExcept]


end RwShared.Properties
