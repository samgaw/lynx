module
public import Runtime.Unwind.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.UnwindProperties

private theorem discard_unit (computation : NativeM Unit) :
    (do computation; Result.ok ()) = computation := by
  have unit_id : (fun _ : Unit => (Result.ok () : NativeM Unit)) = Result.ok := by
    funext token
    cases token
    rfl
  simp only [unit_id, Result.bind_ok]

/-- The callee consumes its owner on both the normal and compiler-unwind paths. -/
theorem callee_contract (mutex : NativeMutex U64) (accepted : Bool) :
    effects_core.assert_then_release mutex accepted =
      (do NativeMutex.dispose mutex
          if accepted then Result.ok () else NativeM.fail .panic) := by
  cases accepted <;> simp [effects_core.assert_then_release, NativeDrop.drop, discard_unit]

/-- The actual owning callee removes exactly its cell before propagating panic. -/
theorem callee_state (mutex : NativeMutex U64) (value : U64) (accepted : Bool)
    (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName U64,
        .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value])]) :
    effects_core.assert_then_release mutex accepted env =
      (if accepted then .ok () else .error (.error (.atom "rust_panicked")),
        { env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != mutex.id) }) := by
  rw [callee_contract]
  cases accepted <;>
    simp [NativeMutex.dispose, NativeM.readCell, NativeM.removeCell, stored, NativeM.fail]

/-- An assertion with a live local owner preserves the prior heap after unwind. -/
theorem local_cleanup (value : U64) (accepted : Bool) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    mutex_assert_scalar value accepted env =
      (if accepted then .ok () else .error (.error (.atom "rust_panicked")),
        { env with refCounter := env.refCounter + 1 }) := by
  have lifecycle := NativeMutex.new_dispose_next value
    (if accepted then Result.ok () else NativeM.fail .panic) env fresh
  cases accepted <;>
    simpa [mutex_assert_scalar, NativeDrop.drop, NativeM.fail, discard_unit] using lifecycle

/-- The caller composes the checked callee's actual unwind behavior. -/
theorem composed_cleanup (value : U64) (accepted : Bool) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    mutex_assert_release value accepted env =
      (if accepted then .ok () else .error (.error (.atom "rust_panicked")),
        { env with refCounter := env.refCounter + 1 }) := by
  have lifecycle := NativeMutex.new_dispose_next value
    (if accepted then Result.ok () else NativeM.fail .panic) env fresh
  cases accepted <;>
    simpa [mutex_assert_release, callee_contract, NativeM.fail, discard_unit] using lifecycle

/-- Either rejected assertion performs cleanup, including the second failure path. -/
theorem repeated_cleanup (value : U64) (first second : Bool) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    mutex_two_assertions value first second env =
      (if first && second then .ok () else .error (.error (.atom "rust_panicked")),
        { env with refCounter := env.refCounter + 1 }) := by
  have lifecycle := NativeMutex.new_dispose_next value
    (if first && second then Result.ok () else NativeM.fail .panic) env fresh
  cases first <;> cases second <;>
    simpa [mutex_two_assertions, NativeDrop.drop, NativeM.fail, discard_unit] using lifecycle

end Runtime.UnwindProperties
