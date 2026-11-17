module
public import __PREFIX__.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx experiment_nif
open __PREFIX__.Extraction.OrderedCollections
namespace __PREFIX__.ResourceProperties

theorem cleanup_contract (value : RegistryState) :
    RegistryState.drop_owned value = (do
      NativeMutex.disposeWith (fun (_ : Map) => NativeM.ok ()) value.table
      NativeMutex.disposeWith (fun (_ : Set) => NativeM.ok ()) value.claims) := by rfl

@[expose] def cells (table : Map) (claims : Set) (mapPoison setPoison : Bool) : List (Nat × String × Term) := [
  (1, NativeMutex.typeName Map, .tuple #[.atom "unlocked", .atom (if mapPoison then "poisoned" else "unpoisoned"), NativeCodec.encode table]),
  (2, NativeMutex.typeName Set, .tuple #[.atom "unlocked", .atom (if setPoison then "poisoned" else "unpoisoned"), NativeCodec.encode claims])]

theorem cleanup_run (table : Map) (claims : Set) (mapPoison setPoison : Bool)
    (env : Environment) (schedule : List ScheduleChoice) :
    (RegistryState.drop_owned ⟨⟨1⟩, ⟨2⟩⟩).run {env with nativeHeap := cells table claims mapPoison setPoison} schedule =
      (.ok (), {env with nativeHeap := []}) := by
  cases mapPoison <;> cases setPoison <;>
    simp [cleanup_contract, cells, NativeMutex.disposeWith, NativeMutex.into_inner,
      NativeMutex.intoInnerStep, NativeCodec.roundtrip, NativeM.ok, Result.wait_run, Result.wait_bind]

@[expose] def live (table : Map) (claims : Set) (mapPoison setPoison : Bool) (env : Environment) : Environment :=
  {env with nativeRefCounter := 4, nativeHeap := [
    (4, NativeResourceArc.handleType RegistryState, .nativeReference 3),
    (3, NativeResourceArc.typeName RegistryState, .tuple #[.integer 1, NativeCodec.encode (RegistryState.mk ⟨1⟩ ⟨2⟩)])]
    ++ cells table claims mapPoison setPoison}

theorem final_release (table : Map) (claims : Set) (mapPoison setPoison : Bool) (env : Environment)
    (policy : env.nativeFinalizerMode = .synchronous) :
    registry_release ⟨3, 4⟩ (live table claims mapPoison setPoison env) =
      (.ok (), {env with nativeRefCounter := 4, nativeHeap := []}) := by
  have released := NativeResourceArc.releaseOwned_last_run_next
    (⟨3, 4⟩ : NativeResourceArc RegistryState) (RegistryState.mk ⟨1⟩ ⟨2⟩) NativeM.ok
    (live table claims mapPoison setPoison env)
    {env with nativeRefCounter := 4, nativeHeap := []}
    (.inr (by simpa [live] using policy))
    (by simp [live, cells]) (by simp [live, cells])
    (by simp [live, cells, NativeResourceArc.handleType, NativeResourceArc.typeName])
    (by
      intro next
      cases mapPoison <;> cases setPoison <;>
        simp [NativeResourceCleanup.cleanup, cleanup_contract, NativeMutex.disposeWith,
          NativeMutex.into_inner, NativeMutex.intoInnerStep, NativeResourceArc.retiredState,
          live, cells, NativeCodec.roundtrip, NativeM.ok, Result.wait_bind, Result.wait_run])
  have identity : (NativeResourceArc.releaseOwned (⟨3, 4⟩ : NativeResourceArc RegistryState) >>= NativeM.ok) =
      NativeResourceArc.releaseOwned (⟨3, 4⟩ : NativeResourceArc RegistryState) := Result.bind_ok _
  rw [identity] at released
  simpa [registry_release, monadLift_self, NativeOwnedDrop.drop, NativeM.ok] using released
end __PREFIX__.ResourceProperties
