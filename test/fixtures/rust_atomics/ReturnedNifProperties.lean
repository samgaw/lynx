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

theorem facade_result (owner : NativeResourceArc Counter) (mode : U64) :
    __RESULT__ owner mode = counter_result owner mode := by
  have propagate (result : core.result.Result (core.result.Result U64 Rustler.DecoderError) Unit) :
      (match result with | .Ok _ => Result.ok result | .Err _ => Result.ok (.Err ())) = Result.ok result := by
    cases result with
    | Ok value => rfl
    | Err error => cases error; rfl
  unfold __RESULT__
  change (counter_result owner mode >>= fun result =>
    match result with | .Ok _ => Result.ok result | .Err _ => Result.ok (.Err ())) = _
  rw [funext propagate]
  simp
