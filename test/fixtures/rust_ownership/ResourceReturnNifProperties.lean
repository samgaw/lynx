module
public import Returned.Properties
public import Returned.RustlerBridge
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace Returned.Properties

theorem resource_reference_eq (left right : Nat) :
    (Term.nativeReference left == Term.nativeReference right) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  rw [Term.beq_iff_compare_eq, Term.compare_eq_reference]
  simp

theorem allocations_distinct : (Term.nativeReference 3 == Term.nativeReference 1) = false := by
  apply Bool.eq_false_iff.mpr
  intro equal
  have same := (Term.compare_eq_reference _ _).mp ((Term.beq_iff_compare_eq _ _).mp equal)
  cases same

theorem facade_return (value accepted : Bool) :
    __ALLOCATE__ value accepted = allocate_resource value accepted := by
  have propagate (result : core.result.Result (NativeResourceArc UnwindResource) Unit) :
      (match result with
        | .Ok _ => Lynx.Result.ok result
        | .Err _ => Lynx.Result.ok (.Err ())) = Lynx.Result.ok result := by
    cases result with
    | Ok value => rfl
    | Err error => cases error; rfl
  unfold __ALLOCATE__
  change (allocate_resource value accepted >>= fun result =>
    match result with
    | .Ok _ => Lynx.Result.ok result
    | .Err _ => Lynx.Result.ok (.Err ())) = _
  rw [funext propagate]
  simp

theorem inner_return (resource : NativeResourceArc UnwindResource) (accepted : Bool) :
    checked_resource_inner resource accepted = (do
      let contents ← NativeResourceArc.deref resource
      NativeResourceArc.release resource
      NativeM.ok (if accepted then core.result.Result.Ok (!contents.value) else core.result.Result.Err ())) := by
  cases accepted <;> simp [checked_resource_inner, checked, NativeM.ok, NativeDrop.drop,
    NativeUnwindDrop.drop]

theorem facade_checked (resource : NativeResourceArc UnwindResource) (accepted : Bool) :
    __CHECKED__ resource accepted = (do
      let retained ← NativeResourceArc.clone resource
      let contents ← NativeResourceArc.deref retained
      NativeResourceArc.release retained
      NativeResourceArc.release resource
      NativeM.ok (if accepted then core.result.Result.Ok (!contents.value) else core.result.Result.Err ())) := by
  cases accepted <;> simp [__CHECKED__,
    inner_return, NativeM.ok, NativeDrop.drop, NativeUnwindDrop.drop, bind_assoc]

@[expose] def initial : Environment :=
  {nativeResourceTypes := [NativeResourceArc.typeName UnwindResource]}

@[expose] def pinned (value : Bool) (counter : Nat) : Environment :=
  {initial with
    nativeRefCounter := counter
    nativeHeap := NativeResourceArc.vmCells ({value := !value} : UnwindResource) 3 5 6}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem encoded_return (value accepted : Bool) :
    (Rustler.executeNative (do
      let owner ← NativeM.resumeCaptured (__ALLOCATE__ value accepted)
      let term ← NativeResourceArc.encode owner
      NativeResourceArc.release owner
      Result.ok term) id).run initial [] =
    if accepted then (.ok (.nativeReference 6), pinned value 6)
    else (.error (.error (.atom "nif_panicked")), {initial with nativeRefCounter := 2}) := by
  have different : (Term.nativeReference 3 == Term.nativeReference 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    have same := (Term.compare_eq_reference _ _).mp ((Term.beq_iff_compare_eq _ _).mp equal)
    cases same
  cases value <;> cases accepted <;> simp [initial, pinned, NativeResourceArc.vmCells, allocate,
    __ALLOCATE__,
    NativeM.resumeCaptured, NativeM.capturePanic, NativeM.ok, NativeM.fail,
    Rustler.executeNative, Result.handle, NativeResourceArc.newCaptured,
    NativeResourceArc.new, NativeResourceArc.deref, NativeResourceArc.release,
    NativeResourceArc.takeOwner, NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.ownership, NativeResourceArc.handleType, NativeResourceArc.typeName,
    NativeResourceArc.termType, NativeResourceArc.referenceLimit, NativeResourceArc.clone,
    NativeResourceArc.encode_eq, NativeResourceArc.decode_eq, NativeCodec.roundtrip,
    NativeM.allocate, List.filter, List.map, different]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem encoded_next {β : Type} (value accepted : Bool) (next : Term → Result β)
    (schedule : List ScheduleChoice) :
    (do
      let encoded ← Rustler.executeNative (do
        let owner ← NativeM.resumeCaptured (__ALLOCATE__ value accepted)
        let term ← NativeResourceArc.encode owner
        NativeResourceArc.release owner
        Result.ok term) id
      next encoded).run initial schedule =
    if accepted then (next (.nativeReference 6)).run (pinned value 6) schedule
    else (.error (.error (.atom "nif_panicked")), {initial with nativeRefCounter := 2}) := by
  have different : (Term.nativeReference 3 == Term.nativeReference 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    have same := (Term.compare_eq_reference _ _).mp ((Term.beq_iff_compare_eq _ _).mp equal)
    cases same
  cases value <;> cases accepted <;> simp [initial, pinned, NativeResourceArc.vmCells, allocate,
    __ALLOCATE__,
    NativeM.resumeCaptured, NativeM.capturePanic, NativeM.ok, NativeM.fail,
    Rustler.executeNative, Result.handle, NativeResourceArc.newCaptured,
    NativeResourceArc.new, NativeResourceArc.deref, NativeResourceArc.release,
    NativeResourceArc.takeOwner, NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.ownership, NativeResourceArc.handleType, NativeResourceArc.typeName,
    NativeResourceArc.termType, NativeResourceArc.referenceLimit, NativeResourceArc.clone,
    NativeResourceArc.encode_eq, NativeResourceArc.decode_eq, NativeCodec.roundtrip,
    NativeM.allocate, List.filter, List.map, different]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem decoded_return (value : Bool) :
    (do
      let owner ← NativeM.resumeCaptured (__ALLOCATE__ value true)
      let term ← NativeResourceArc.encode owner
      NativeResourceArc.release owner
      let decoded ← NativeResourceArc.decode (α := UnwindResource) term
      NativeM.resumeCaptured (__CHECKED__ decoded true)).run initial [] =
      (.ok value, pinned value 8) := by
  have different : (Term.nativeReference 3 == Term.nativeReference 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    have same := (Term.compare_eq_reference _ _).mp ((Term.beq_iff_compare_eq _ _).mp equal)
    cases same
  cases value <;> simp [initial, pinned, NativeResourceArc.vmCells, allocate,
    __ALLOCATE__,
    NativeM.resumeCaptured, NativeM.capturePanic, NativeM.ok, NativeM.fail,
    Rustler.executeNative, Result.handle, NativeResourceArc.newCaptured,
    NativeResourceArc.new, NativeResourceArc.deref, NativeResourceArc.release,
    NativeResourceArc.takeOwner, NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.ownership, NativeResourceArc.handleType, NativeResourceArc.typeName,
    NativeResourceArc.termType, NativeResourceArc.referenceLimit, NativeResourceArc.clone,
    NativeResourceArc.encode_eq, NativeResourceArc.decode_eq, NativeCodec.roundtrip,
    NativeM.allocate, List.filter, List.map, different,
    __CHECKED__,
    checked_resource_inner, checked, NativeDrop.drop, NativeUnwindDrop.drop]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem adapter_roundtrip (value : Bool) :
    (do
      let term ← Rustler.executeNative (do
        let owner ← NativeM.resumeCaptured (__ALLOCATE__ value true)
        let term ← NativeResourceArc.encode owner
        NativeResourceArc.release owner
        Result.ok term) id
      let decoded ← NativeResourceArc.decode (α := UnwindResource) term
      Rustler.executeNative (NativeM.resumeCaptured
        (__CHECKED__ decoded true)) Rustler.encodeBool).run initial [] =
      (.ok (Rustler.encodeBool value), pinned value 8) := by
  have different : (Term.nativeReference 3 == Term.nativeReference 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    have same := (Term.compare_eq_reference _ _).mp ((Term.beq_iff_compare_eq _ _).mp equal)
    cases same
  cases value <;> simp [initial, pinned, NativeResourceArc.vmCells, allocate,
    __ALLOCATE__,
    NativeM.resumeCaptured, NativeM.capturePanic, NativeM.ok, NativeM.fail,
    Rustler.executeNative, Result.handle, NativeResourceArc.newCaptured,
    NativeResourceArc.new, NativeResourceArc.deref, NativeResourceArc.release,
    NativeResourceArc.takeOwner, NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.ownership, NativeResourceArc.handleType, NativeResourceArc.typeName,
    NativeResourceArc.termType, NativeResourceArc.referenceLimit, NativeResourceArc.clone,
    NativeResourceArc.encode_eq, NativeResourceArc.decode_eq, NativeCodec.roundtrip,
    NativeM.allocate, List.filter, List.map, different,
    __CHECKED__,
    checked_resource_inner, checked, NativeDrop.drop, NativeUnwindDrop.drop]

end Returned.Properties
