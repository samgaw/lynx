module
public import ResourceInternal.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace ResourceInternal.Properties

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


end ResourceInternal.Properties
