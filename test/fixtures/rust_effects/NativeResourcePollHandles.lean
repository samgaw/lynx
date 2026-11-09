module
public import Shared.Properties
public import Shared.Future
public section
open Aeneas Aeneas.Std Lynx effects_native Shared.Properties
namespace Shared.PollProperties

theorem cancel_call_next {α : Type} (env : Environment) (value amount : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (next : Term → NativeM α)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference 5)
      let result ← Rustler.executeNative (__CANCEL__ owner amount) Rustler.encodeBool
      next result) (pinnedEnv env value counter) =
      next Term.true (pinnedEnv env value (counter+1)) := by
  rw [decode_next env value counter bounded _ registered]
  simp only [Rustler.executeNative, Shared.Future.cancel_contract,
    monadLift_self, bind_assoc, NativeM.ok, Result.ok_bind]
  rw [show decodedEnv env value counter = ownedEnv env value (counter+1) (counter+1) from rfl]
  simp only [release_handled_next env value (counter+1) (counter+1) (by omega)]
  simp [Result.handle, Rustler.encodeBool, Term.true]

theorem cancel_call_at {α : Type} (env : Environment) (value amount : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (next : Term → NativeM α)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 2 4 5 ++ [cell value])
    (count : env.nativeRefCounter = counter)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference 5)
      let result ← Rustler.executeNative (__CANCEL__ owner amount) Rustler.encodeBool
      next result) env =
      next Term.true (pinnedEnv env value (counter+1)) := by
  have same : pinnedEnv env value counter = env := by
    cases env
    simp_all [pinnedEnv]
  simpa only [same] using cancel_call_next env value amount counter bounded next registered

end Shared.PollProperties
