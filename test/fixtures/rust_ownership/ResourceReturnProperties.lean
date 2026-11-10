module
public import Returned.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace Returned.Properties

theorem mutate (value accepted : Bool) :
    ownership_base.mutate_before_check value accepted = NativeM.ok
      ((if accepted then core.result.Result.Ok () else core.result.Result.Err ()), !value) := by
  cases accepted <;> simp [ownership_base.mutate_before_check, NativeM.ok]

theorem checked (value accepted : Bool) :
    ownership_app.checked_value value accepted = NativeM.ok
      ((if accepted then core.result.Result.Ok () else core.result.Result.Err ()), !value) := by
  cases accepted <;> simp [ownership_app.checked_value, mutate, NativeM.ok]

theorem allocate (value accepted : Bool) :
    allocate_resource value accepted = (do
      let result ← NativeResourceArc.newCaptured ({value} : UnwindResource)
      match result with
      | .Ok original => do
        let contents ← NativeResourceArc.deref original
        if accepted then
          let returned ← NativeResourceArc.newCaptured ({value := !contents.value} : UnwindResource)
          NativeResourceArc.release original
          NativeM.ok returned
        else
          NativeResourceArc.release original
          NativeM.ok (.Err ())
      | .Err _ => NativeM.ok (.Err ())) := by
  have finish (original : NativeResourceArc UnwindResource)
      (returned : core.result.Result (NativeResourceArc UnwindResource) Unit) :
      (match returned with
        | .Ok _ => do original.release; Lynx.Result.ok returned
        | .Err _ => do original.release; Lynx.Result.ok (.Err ())) =
      (do original.release; Lynx.Result.ok returned) := by
    cases returned with
    | Ok _ => rfl
    | Err error => cases error; rfl
  cases accepted <;> simp [allocate_resource, checked, NativeM.ok, NativeDrop.drop,
    NativeUnwindDrop.drop, bind_assoc]
  · rfl
  · congr 1
    funext result
    cases result with
    | Err _ => rfl
    | Ok original =>
      dsimp only
      congr 1
      funext contents
      congr 1
      funext returned
      exact finish original returned

@[expose] def empty (env : Environment) : Environment :=
  {env with nativeRefCounter := 0, nativeHeap := []}

@[expose] def returned (env : Environment) (value : Bool) : Environment :=
  {empty env with nativeRefCounter := 4, nativeHeap := [
    (4, NativeResourceArc.handleType UnwindResource, .nativeReference 3),
    (3, NativeResourceArc.typeName UnwindResource,
      .tuple #[.integer 1, NativeCodec.encode ({value := !value} : UnwindResource)])]}

set_option maxHeartbeats 800000 in
theorem allocate_registered (env : Environment) (value accepted : Bool)
    (registered : NativeResourceArc.typeName UnwindResource ∈ env.nativeResourceTypes)
    (schedule : List ScheduleChoice) :
    (allocate_resource value accepted).run (empty env) schedule =
      if accepted then (.ok (.Ok ⟨3, 4⟩), returned env value)
      else (.ok (.Err ()), {empty env with nativeRefCounter := 2}) := by
  have reg := registered
  simp [NativeResourceArc.typeName] at reg
  have different : (Term.nativeReference 3 == Term.nativeReference 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    have same := (Term.compare_eq_reference _ _).mp ((Term.beq_iff_compare_eq _ _).mp equal)
    cases same
  cases accepted <;> simp [allocate, empty, returned, different, NativeResourceArc.newCaptured,
    NativeM.capturePanic, NativeResourceArc.new, NativeResourceArc.deref,
    NativeResourceArc.release, NativeResourceArc.takeOwner, NativeResourceArc.ownerState,
    NativeResourceArc.retiredState, NativeResourceArc.ownership, NativeResourceArc.handleType,
    NativeResourceArc.typeName, NativeResourceArc.referenceLimit, NativeCodec.roundtrip,
    NativeM.allocate, NativeM.ok, NativeM.fail, Result.handle, reg, List.filter]

set_option maxHeartbeats 800000 in
theorem allocate_unregistered (env : Environment) (value accepted : Bool)
    (missing : NativeResourceArc.typeName UnwindResource ∉ env.nativeResourceTypes)
    (schedule : List ScheduleChoice) :
    (allocate_resource value accepted).run env schedule = (.ok (.Err ()), env) := by
  have absent := missing
  simp [NativeResourceArc.typeName] at absent
  simp [allocate, NativeResourceArc.newCaptured, NativeM.capturePanic, NativeResourceArc.new,
    NativeM.fail, NativeM.ok, Result.handle, NativeResourceArc.typeName, absent]

end Returned.Properties
