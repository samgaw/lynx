module
public import Runtime.Ownership.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.OwnershipProperties

/-- A contract over the extracted callee, including its failure continuation. -/
theorem release_contract (mutex : NativeMutex U64) (accepted : Bool) :
    effects_core.release_checked mutex accepted =
      (do NativeMutex.dispose mutex; NativeM.massert accepted) := by
  rfl

/-- Owning-argument consumption preserves every unrelated cell, even on panic. -/
theorem release_state (mutex : NativeMutex U64) (value : U64) (accepted : Bool)
    (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName U64,
        .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value])]) :
    effects_core.release_checked mutex accepted env =
      (if accepted then .ok () else .error (.error (.atom "rust_panicked")),
        { env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != mutex.id) }) := by
  rw [release_contract]
  cases accepted <;>
    simp [NativeMutex.dispose, NativeM.readCell, NativeM.removeCell, stored,
      NativeM.massert, NativeM.fail]

/-- The caller composes the checked callee contract without losing cleanup on failure. -/
theorem composed_release (value : U64) (accepted : Bool) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    mutex_release_checked value accepted env =
      (if accepted then .ok () else .error (.error (.atom "rust_panicked")),
        { env with refCounter := env.refCounter + 1 }) := by
  have lifecycle := NativeMutex.new_dispose_next value (NativeM.massert accepted) env fresh
  cases accepted <;>
    simpa [mutex_release_checked, release_contract, NativeM.massert, NativeM.fail] using lifecycle

end Runtime.OwnershipProperties
