module
public import Resource.Extraction.Funs
public import Resource.RustlerBridge
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace Resource.Properties

theorem mutate (value accepted : Bool) :
    ownership_base.mutate_before_check value accepted = NativeM.ok
      ((if accepted then core.result.Result.Ok () else core.result.Result.Err ()), !value) := by
  cases accepted <;> simp [ownership_base.mutate_before_check, NativeM.ok]

theorem checked (value accepted : Bool) :
    ownership_app.checked_value value accepted = NativeM.ok
      ((if accepted then core.result.Result.Ok () else core.result.Result.Err ()), !value) := by
  cases accepted <;> simp [ownership_app.checked_value, mutate, NativeM.ok]

theorem inner (resource : NativeResourceArc UnwindResource) (accepted : Bool) :
    checked_resource_inner resource accepted = (do
      let contents ← NativeResourceArc.deref resource
      NativeResourceArc.release resource
      NativeM.ok (if accepted then core.result.Result.Ok (!contents.value) else core.result.Result.Err ())) := by
  cases accepted <;> simp [checked_resource_inner, checked, NativeM.ok, NativeDrop.drop,
    NativeUnwindDrop.drop]

theorem facade (resource : NativeResourceArc UnwindResource) (accepted : Bool) :
    __RESOURCE__ resource accepted = (do
      let retained ← NativeResourceArc.clone resource
      let contents ← NativeResourceArc.deref retained
      NativeResourceArc.release retained
      NativeResourceArc.release resource
      NativeM.ok (if accepted then core.result.Result.Ok (!contents.value) else core.result.Result.Err ())) := by
  cases accepted <;> simp [__RESOURCE__,
    inner, NativeM.ok, NativeDrop.drop, NativeUnwindDrop.drop, bind_assoc]

@[expose] def ownedEnv (env : Environment) (value : Bool) : Environment :=
  {env with nativeRefCounter := 2, nativeHeap := [
    (2, NativeResourceArc.handleType UnwindResource, .nativeReference 1),
    (1, NativeResourceArc.typeName UnwindResource,
      .tuple #[.integer 1, NativeCodec.encode ({value} : UnwindResource)])]}

theorem inner_final (env : Environment) (value accepted : Bool) :
    checked_resource_inner ⟨1,2⟩ accepted (ownedEnv env value) =
      (.ok (if accepted then core.result.Result.Ok (!value) else core.result.Result.Err ()),
       {env with nativeRefCounter := 2, nativeHeap := []}) := by
  rw [inner]
  cases accepted <;> simp [ownedEnv, NativeResourceArc.deref, NativeResourceArc.release,
    NativeResourceArc.takeOwner, NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.ownership, NativeResourceArc.handleType, NativeResourceArc.typeName,
    NativeResourceArc.referenceLimit, NativeCodec.roundtrip, NativeM.ok, List.filter, List.map]

theorem facade_final (env : Environment) (value accepted : Bool) :
    __RESOURCE__
        ⟨1,2⟩ accepted (ownedEnv env value) =
      (.ok (if accepted then core.result.Result.Ok (!value) else core.result.Result.Err ()),
       {env with nativeRefCounter := 3, nativeHeap := []}) := by
  rw [facade]
  cases accepted <;> simp [ownedEnv, NativeResourceArc.clone, NativeResourceArc.deref,
    NativeResourceArc.release, NativeResourceArc.takeOwner, NativeResourceArc.ownerState,
    NativeResourceArc.retiredState, NativeResourceArc.ownership, NativeResourceArc.handleType,
    NativeResourceArc.typeName, NativeResourceArc.referenceLimit, NativeCodec.roundtrip, NativeM.ok, List.filter, List.map]

@[expose] def pinnedEnv (env : Environment) (value : Bool) (counter : Nat) : Environment :=
  {env with
    nativeRefCounter := counter
    nativeHeap := NativeResourceArc.vmCells ({value} : UnwindResource) 1 2 3}

set_option maxHeartbeats 800000 in
theorem adapter_continuation {β : Type} (env : Environment) (value accepted : Bool)
    (counter : Nat) (bound : 3 ≤ counter) (next : Term → Result β)
    (registered : NativeResourceArc.typeName UnwindResource ∈ env.nativeResourceTypes)
    (schedule : List ScheduleChoice) :
    (do
      let resource ← NativeResourceArc.decode (.nativeReference 3)
      let encoded ← Rustler.executeNative (NativeM.resumeCaptured
        (__RESOURCE__ resource accepted)) Rustler.encodeBool
      next encoded).run (pinnedEnv env value counter) schedule =
      if accepted then (next (Rustler.encodeBool (!value))).run (pinnedEnv env value (counter + 2)) schedule
      else (.error (.error (.atom "nif_panicked")), pinnedEnv env value (counter + 2)) := by
  have reg := registered
  simp [NativeResourceArc.typeName] at reg
  have zero : counter ≠ 0 := by omega
  have one : counter ≠ 1 := by omega
  have two : counter ≠ 2 := by omega
  have z0 : (counter == 0) = false := by simp [zero]
  have z1 : (counter == 1) = false := by simp [one]
  have z2 : (counter == 2) = false := by simp [two]
  have different : (counter + 1 == counter + 2) = false := by simp
  cases accepted <;>
    simp [facade, NativeM.resumeCaptured, NativeM.fail, NativeM.ok, Rustler.executeNative,
      Result.handle, pinnedEnv, NativeResourceArc.vmCells, NativeResourceArc.decode_eq,
      NativeResourceArc.clone,
      NativeResourceArc.deref, NativeResourceArc.release, NativeResourceArc.takeOwner,
      NativeResourceArc.ownerState, NativeResourceArc.ownership,
      NativeResourceArc.handleType, NativeResourceArc.typeName, NativeResourceArc.termType,
      NativeResourceArc.referenceLimit, NativeCodec.roundtrip, reg,
      bne, z0,z1,z2,different, zero,
      Nat.add_assoc, List.filter, List.map]

end Resource.Properties

namespace Resource.Properties
set_option maxHeartbeats 800000 in
theorem handler_prefix {β γ : Type} (env : Environment) (value accepted : Bool)
    (counter : Nat) (bound : 3 ≤ counter) (tail : Term → Result β)
    (next : β → Result γ) (handler : Exception → Result γ)
    (registered : NativeResourceArc.typeName UnwindResource ∈ env.nativeResourceTypes)
    (schedule : List ScheduleChoice) :
    (Result.tryWith (do
      let resource ← NativeResourceArc.decode (.nativeReference 3)
      let encoded ← Rustler.executeNative (NativeM.resumeCaptured
        (__RESOURCE__ resource accepted)) Rustler.encodeBool
      tail encoded) next handler).run (pinnedEnv env value counter) schedule =
      if accepted then (Result.tryWith (tail (Rustler.encodeBool (!value))) next handler).run
        (pinnedEnv env value (counter + 2)) schedule
      else (handler (.error (.atom "nif_panicked"))).run (pinnedEnv env value (counter + 2)) schedule := by
  have reg := registered
  simp [NativeResourceArc.typeName] at reg
  have zero : counter ≠ 0 := by omega
  have one : counter ≠ 1 := by omega
  have two : counter ≠ 2 := by omega
  have z0 : (counter == 0) = false := by simp [zero]
  have z1 : (counter == 1) = false := by simp [one]
  have z2 : (counter == 2) = false := by simp [two]
  have different : (counter + 1 == counter + 2) = false := by simp
  cases accepted <;>
    simp [facade, NativeM.resumeCaptured, NativeM.fail, NativeM.ok, Rustler.executeNative,
      Result.tryWith, Result.handle, Result.bind, pinnedEnv, NativeResourceArc.vmCells, NativeResourceArc.decode_eq,
      NativeResourceArc.clone,
      NativeResourceArc.deref, NativeResourceArc.release, NativeResourceArc.takeOwner,
      NativeResourceArc.ownerState, NativeResourceArc.ownership,
      NativeResourceArc.handleType, NativeResourceArc.typeName, NativeResourceArc.termType,
      NativeResourceArc.referenceLimit, NativeCodec.roundtrip, reg,
      bne, z0,z1,z2,different, zero,
      Nat.add_assoc, List.filter, List.map]

end Resource.Properties

namespace Resource.Properties
set_option maxHeartbeats 800000 in
theorem decode_error_prefix {β γ : Type} (env : Environment) (value : Bool)
    (counter : Nat) (bound : 3 ≤ counter) (error : Exception) (catchable : error ≠ .exhausted)
    (next : β → Result γ) (handler : Exception → Result γ)
    (registered : NativeResourceArc.typeName UnwindResource ∈ env.nativeResourceTypes)
    (schedule : List ScheduleChoice) :
    (Result.tryWith (do
      let resource ← NativeResourceArc.decode (α := UnwindResource) (.nativeReference 3)
      NativeResourceArc.release resource
      (Result.error error : Result β)) next handler).run (pinnedEnv env value counter) schedule =
      (handler error).run (pinnedEnv env value (counter + 1)) schedule := by
  have reg := registered
  simp [NativeResourceArc.typeName] at reg
  have zero : counter ≠ 0 := by omega
  have z0 : (counter == 0) = false := by simp [zero]
  have z1 : (counter == 1) = false := by simp; omega
  have z2 : (counter == 2) = false := by simp; omega
  cases error <;> try contradiction
  all_goals simp [Result.tryWith, Result.handle, Result.bind, pinnedEnv, NativeResourceArc.vmCells,
    NativeResourceArc.decode_eq, NativeResourceArc.clone, NativeResourceArc.release,
    NativeResourceArc.takeOwner, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.handleType, NativeResourceArc.typeName, NativeResourceArc.termType,
    NativeResourceArc.referenceLimit, NativeCodec.roundtrip, reg, zero, z0,z1,z2,
    bne, List.filter, List.map]

@[expose] def seed : Environment := {
  pdict := [(.atom "held", .nativeReference 3)]
  nativeResourceTypes := [NativeResourceArc.typeName UnwindResource] }

@[expose] def initial : Environment := pinnedEnv seed true 3
end Resource.Properties

namespace Resource.Properties
@[simp] theorem pinned_pdict (env : Environment) (value : Bool) (counter : Nat) :
    (pinnedEnv env value counter).pdict = env.pdict := rfl

@[simp] theorem registry_prefix {α : Type} (env : Environment) (value : Bool)
    (counter : Nat) (types : List String) (computation : Result α) (schedule : List ScheduleChoice) :
    (Rustler.withResourceTypes types computation).run (pinnedEnv env value counter) schedule =
      computation.run (pinnedEnv {env with nativeResourceTypes :=
        (env.nativeResourceTypes ++ types).eraseDups} value counter) schedule := by
  simp [Rustler.withResourceTypes, pinnedEnv]

@[simp] theorem catch_get {α β : Type} (body : Environment → Result α)
    (next : α → Result β) (handler : Exception → Result β) :
    Result.tryWith (.get body) next handler =
      .get (fun env => Result.tryWith (body env) next handler) := rfl

@[simp] theorem catch_modify {α β γ : Type} (transition : Environment → α × Environment)
    (body : α → Result β) (next : β → Result γ) (handler : Exception → Result γ) :
    Result.tryWith (.nativeModify transition body) next handler =
      .nativeModify transition (fun value => Result.tryWith (body value) next handler) := rfl
end Resource.Properties

namespace Resource.Properties
@[simp] theorem registry_bind {α β : Type} (types : List String)
    (computation : Result α) (next : α → Result β) :
    (Rustler.withResourceTypes types computation >>= next) =
      Rustler.withResourceTypes types (computation >>= next) := rfl

@[simp] theorem catch_registry {α β : Type} (types : List String)
    (computation : Result α) (next : α → Result β) (handler : Exception → Result β) :
    Result.tryWith (Rustler.withResourceTypes types computation) next handler =
      Rustler.withResourceTypes types (Result.tryWith computation next handler) := rfl
end Resource.Properties

namespace Resource.Properties
@[simp] theorem handle_registry {α : Type} (types : List String)
    (computation : Result α) (handler : Exception → Result α) :
    Result.handle (Rustler.withResourceTypes types computation) handler =
      Rustler.withResourceTypes types (Result.handle computation handler) := rfl
end Resource.Properties
