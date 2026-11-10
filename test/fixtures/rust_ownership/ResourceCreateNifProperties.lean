module
public import Created.Properties
public import Created.RustlerBridge
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace Created.Properties

theorem facade (value accepted : Bool) :
    __CREATED__ value accepted = create_checked_resource value accepted := by
  have propagate (result : core.result.Result Bool Unit) :
      (match result with
        | .Ok _ => Lynx.Result.ok result
        | .Err _ => Lynx.Result.ok (.Err ())) = Lynx.Result.ok result := by
    cases result with
    | Ok value => rfl
    | Err error => cases error; rfl
  unfold __CREATED__
  change (create_checked_resource value accepted >>= fun result =>
    match result with
    | .Ok _ => Lynx.Result.ok result
    | .Err _ => Lynx.Result.ok (.Err ())) = _
  rw [funext propagate]
  simp

set_option maxHeartbeats 800000 in
theorem adapter_continuation {β : Type} (env : Environment) (value accepted : Bool)
    (heap : env.nativeHeap = [])
    (registered : NativeResourceArc.typeName UnwindResource ∈ env.nativeResourceTypes)
    (next : Term → Result β) (schedule : List ScheduleChoice) :
    (do
      let encoded ← Rustler.executeNative (NativeM.resumeCaptured
        (__CREATED__ value accepted)) Rustler.encodeBool
      next encoded).run env schedule =
      if accepted then (next (Rustler.encodeBool (!value))).run {env with nativeRefCounter := env.nativeRefCounter + 2} schedule
      else (.error (.error (.atom "nif_panicked")), {env with nativeRefCounter := env.nativeRefCounter + 2}) := by
  have reg := registered
  simp [NativeResourceArc.typeName] at reg
  have forward : env.nativeRefCounter ≠ env.nativeRefCounter + 1 := by omega
  have backward : env.nativeRefCounter + 1 ≠ env.nativeRefCounter := by omega
  have first : (env.nativeRefCounter == env.nativeRefCounter + 1) = false := by simp [forward]
  have second : (env.nativeRefCounter + 1 == env.nativeRefCounter) = false := by simp [backward]
  cases accepted <;> simp [facade, create, NativeM.resumeCaptured, NativeM.capturePanic,
      NativeResourceArc.newCaptured, NativeResourceArc.new, NativeResourceArc.deref,
      NativeResourceArc.release, NativeResourceArc.takeOwner, NativeResourceArc.ownerState,
      NativeResourceArc.retiredState, NativeResourceArc.ownership, NativeResourceArc.handleType,
      NativeResourceArc.typeName, NativeResourceArc.referenceLimit, NativeCodec.roundtrip,
      NativeM.allocate, NativeM.ok, NativeM.fail, Rustler.executeNative,
      Result.handle, heap, reg, List.filter, bne, Nat.add_assoc, first, second]

set_option maxHeartbeats 800000 in
theorem adapter_handled {β γ : Type} (env : Environment) (value accepted : Bool)
    (heap : env.nativeHeap = [])
    (registered : NativeResourceArc.typeName UnwindResource ∈ env.nativeResourceTypes)
    (tail : Term → Result β) (next : β → Result γ) (handler : Exception → Result γ)
    (schedule : List ScheduleChoice) :
    (Result.tryWith (do
      let encoded ← Rustler.executeNative (NativeM.resumeCaptured
        (__CREATED__ value accepted)) Rustler.encodeBool
      tail encoded) next handler).run env schedule =
      if accepted then (Result.tryWith (tail (Rustler.encodeBool (!value))) next handler).run
        {env with nativeRefCounter := env.nativeRefCounter + 2} schedule
      else (handler (.error (.atom "nif_panicked"))).run {env with nativeRefCounter := env.nativeRefCounter + 2} schedule := by
  have reg := registered
  simp [NativeResourceArc.typeName] at reg
  have forward : env.nativeRefCounter ≠ env.nativeRefCounter + 1 := by omega
  have backward : env.nativeRefCounter + 1 ≠ env.nativeRefCounter := by omega
  have first : (env.nativeRefCounter == env.nativeRefCounter + 1) = false := by simp [forward]
  have second : (env.nativeRefCounter + 1 == env.nativeRefCounter) = false := by simp [backward]
  cases accepted <;> simp [facade, create, NativeM.resumeCaptured, NativeM.capturePanic,
      NativeResourceArc.newCaptured, NativeResourceArc.new, NativeResourceArc.deref,
      NativeResourceArc.release, NativeResourceArc.takeOwner, NativeResourceArc.ownerState,
      NativeResourceArc.retiredState, NativeResourceArc.ownership, NativeResourceArc.handleType,
      NativeResourceArc.typeName, NativeResourceArc.referenceLimit, NativeCodec.roundtrip,
      NativeM.allocate, NativeM.ok, NativeM.fail, Rustler.executeNative,
      Result.handle, heap, reg, List.filter, bne, Nat.add_assoc, first, second, Result.tryWith, Result.bind]

@[simp] theorem catch_modify {α β γ : Type} (transition : Environment → α × Environment)
    (body : α → Lynx.Result β) (next : β → Lynx.Result γ) (handler : Exception → Lynx.Result γ) :
    Lynx.Result.tryWith (.nativeModify transition body) next handler =
      .nativeModify transition (fun value => Lynx.Result.tryWith (body value) next handler) := rfl

end Created.Properties
