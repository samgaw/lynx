module
public import Atomic.ResourceProperties
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Atomic.ResourceProperties

theorem facade_new (value : U64) : __NEW__ value = counter_new value := by
  have propagate (result : core.result.Result (NativeResourceArc Counter) Unit) :
      (match result with
        | .Ok _ => Result.ok result
        | .Err _ => Result.ok (.Err ())) = Result.ok result := by
    cases result with
    | Ok value => rfl
    | Err error => cases error; rfl
  unfold __NEW__
  change (counter_new value >>= fun result =>
    match result with | .Ok _ => Result.ok result | .Err _ => Result.ok (.Err ())) = _
  rw [funext propagate]
  simp

theorem facade_claim (owner : NativeResourceArc Counter) :
    __CLAIM__ owner = counter_claim owner := by rfl

theorem facade_pair (owner : NativeResourceArc Counter) :
    __PAIR__ owner = counter_pair owner := by rfl

theorem facade_read (owner : NativeResourceArc Counter) :
    __READ__ owner = counter_read owner := by rfl

theorem facade_checked (value : U64) (accepted : Bool) :
    __CHECKED__ value accepted = counter_checked value accepted := by
  have propagate (result : core.result.Result (U64 × U64) Unit) :
      (match result with
        | .Ok _ => Result.ok result
        | .Err _ => Result.ok (.Err ())) = Result.ok result := by
    cases result with
    | Ok value => rfl
    | Err error => cases error; rfl
  unfold __CHECKED__
  change (counter_checked value accepted >>= fun result =>
    match result with | .Ok _ => Result.ok result | .Err _ => Result.ok (.Err ())) = _
  rw [funext propagate]
  simp
end Atomic.ResourceProperties
