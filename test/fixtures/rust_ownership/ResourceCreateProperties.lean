module
public import Created.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace Created.Properties

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


theorem create (value accepted : Bool) :
    create_checked_resource value accepted = (do
      let result ← NativeResourceArc.newCaptured ({value} : UnwindResource)
      match result with
      | .Ok resource => do
        let contents ← NativeResourceArc.deref resource
        NativeResourceArc.release resource
        NativeM.ok (if accepted then core.result.Result.Ok (!contents.value) else core.result.Result.Err ())
      | .Err _ => NativeM.ok (.Err ())) := by
  cases accepted <;> simp [create_checked_resource, inner, NativeM.ok, bind_assoc]
  all_goals rfl

@[expose] def empty (env : Environment) : Environment :=
  {env with nativeRefCounter := 0, nativeHeap := []}

set_option maxHeartbeats 800000 in
theorem create_registered (env : Environment) (value accepted : Bool)
    (registered : NativeResourceArc.typeName UnwindResource ∈ env.nativeResourceTypes)
    (schedule : List ScheduleChoice) :
    (create_checked_resource value accepted).run (empty env) schedule =
      (.ok (if accepted then core.result.Result.Ok (!value) else core.result.Result.Err ()),
       {empty env with nativeRefCounter := 2}) := by
  have reg := registered
  simp [NativeResourceArc.typeName] at reg
  cases accepted <;> simp [create, empty, NativeResourceArc.newCaptured, NativeM.capturePanic,
    NativeResourceArc.new, NativeResourceArc.deref, NativeResourceArc.release,
    NativeResourceArc.takeOwner, NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.ownership, NativeResourceArc.handleType, NativeResourceArc.typeName,
    NativeResourceArc.referenceLimit, NativeCodec.roundtrip, NativeM.allocate, NativeM.ok,
    NativeM.fail, Result.handle, reg, List.filter]

theorem create_unregistered (env : Environment) (value accepted : Bool)
    (missing : NativeResourceArc.typeName UnwindResource ∉ env.nativeResourceTypes)
    (schedule : List ScheduleChoice) :
    (create_checked_resource value accepted).run env schedule = (.ok (.Err ()), env) := by
  have absent := missing
  simp [NativeResourceArc.typeName] at absent
  simp [create, NativeResourceArc.newCaptured, NativeM.capturePanic, NativeResourceArc.new,
    NativeM.fail, NativeM.ok, Result.handle, NativeResourceArc.typeName, absent]

@[expose] def held (env : Environment) (value poisoned : Bool) : Environment :=
  {env with nativeRefCounter := 1, nativeHeap := [(1, NativeMutex.typeName Bool,
    .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
      NativeCodec.encode value])]}

set_option maxHeartbeats 800000 in
theorem cleanup_registered (env : Environment) (value accepted heldValue poisoned : Bool)
    (registered : NativeResourceArc.typeName UnwindResource ∈ env.nativeResourceTypes)
    (schedule : List ScheduleChoice) :
    (create_with_mutex ⟨1⟩ value accepted).run (held env heldValue poisoned) schedule =
      (.ok (if accepted then core.result.Result.Ok (!value) else core.result.Result.Err ()),
       {empty env with nativeRefCounter := 3}) := by
  have reg := registered
  simp [NativeResourceArc.typeName] at reg
  cases accepted <;> cases poisoned <;>
    simp [create_with_mutex, inner, empty, held, NativeResourceArc.newCaptured, NativeM.capturePanic,
      NativeResourceArc.new, NativeResourceArc.deref, NativeResourceArc.release,
      NativeResourceArc.takeOwner, NativeResourceArc.ownerState, NativeResourceArc.retiredState,
      NativeResourceArc.ownership, NativeResourceArc.handleType, NativeResourceArc.typeName,
      NativeResourceArc.referenceLimit, NativeCodec.roundtrip, NativeM.allocate, NativeM.ok,
      NativeM.fail, Result.handle, NativeDrop.drop, NativeUnwindDrop.drop, NativeMutex.dispose,
      NativeM.readCell, NativeM.removeCell, NativeMutex.typeName, NativeCodec.typeName, reg, List.filter]

theorem cleanup_unregistered (env : Environment) (value accepted heldValue poisoned : Bool)
    (missing : NativeResourceArc.typeName UnwindResource ∉ env.nativeResourceTypes)
    (schedule : List ScheduleChoice) :
    (create_with_mutex ⟨1⟩ value accepted).run (held env heldValue poisoned) schedule =
      (.ok (.Err ()), {empty env with nativeRefCounter := 1}) := by
  have absent := missing
  simp [NativeResourceArc.typeName] at absent
  cases poisoned <;>
    simp [create_with_mutex, NativeResourceArc.newCaptured, NativeM.capturePanic, NativeResourceArc.new,
      NativeM.fail, NativeM.ok, Result.handle, NativeResourceArc.typeName, absent, held, empty,
      NativeUnwindDrop.drop, NativeMutex.dispose, NativeM.readCell, NativeM.removeCell, List.filter]

end Created.Properties
