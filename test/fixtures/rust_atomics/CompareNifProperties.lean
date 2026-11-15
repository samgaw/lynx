/-- The actual consuming resource function delegates to the cross-crate body. -/
theorem resource_contract (owner : NativeResourceArc Counter) (expected replacement : U64) :
    counter_replace owner expected replacement = (do
      let payload ← NativeResourceArc.deref owner
      let result ← atomic_analysis.try_set payload.state expected replacement
      NativeOwnedDrop.drop owner
      NativeM.ok result) := by rfl

theorem facade_new (value : U64) : __NEW__ value = counter_new value := by
  have propagate (result : core.result.Result (NativeResourceArc Counter) Unit) :
      (match result with | .Ok _ => Result.ok result | .Err _ => Result.ok (.Err ())) = Result.ok result := by
    cases result with
    | Ok value => rfl
    | Err error => cases error; rfl
  unfold __NEW__
  change (counter_new value >>= fun result =>
    match result with | .Ok _ => Result.ok result | .Err _ => Result.ok (.Err ())) = _
  rw [funext propagate]
  simp

theorem facade_read (owner : NativeResourceArc Counter) :
    __READ__ owner = counter_read owner := by rfl

theorem facade_replace (owner : NativeResourceArc Counter) (expected replacement : U64) :
    __REPLACE__ owner expected replacement = counter_replace owner expected replacement := by rfl
