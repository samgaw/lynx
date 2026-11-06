module
public import Runtime.Payload.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.PayloadProperties

private theorem discard_unit (computation : NativeM Unit) :
    (do computation; Result.ok ()) = computation := by
  have unit_id : (fun _ : Unit => (Result.ok () : NativeM Unit)) = Result.ok := by
    funext token
    cases token
    rfl
  simp only [unit_id, Result.bind_ok]

/-- The actual destructor-free struct is consumed with its owning mutex. -/
theorem explicit_dispose (value : U64) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    mutex_discard value env = (.ok (), { env with refCounter := env.refCounter + 1 }) := by
  simpa [mutex_discard, NativeDrop.drop] using
    NativeMutex.new_dispose (effects_core.Counter.mk value) env fresh

/-- Compiler-generated scope destruction has the same observable cleanup. -/
theorem scope_dispose (value : U64) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    mutex_scope value env = (.ok (), { env with refCounter := env.refCounter + 1 }) := by
  simpa [mutex_scope, NativeDrop.drop] using
    NativeMutex.new_dispose (effects_core.Counter.mk value) env fresh

/-- Assertion unwind consumes the actual struct's mutex before propagating panic. -/
theorem assertion_cleanup (value : U64) (accepted : Bool) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    mutex_assert value accepted env =
      (if accepted then .ok () else .error (.error (.atom "rust_panicked")),
        { env with refCounter := env.refCounter + 1 }) := by
  have lifecycle := NativeMutex.new_dispose_next (effects_core.Counter.mk value)
    (if accepted then Result.ok () else NativeM.fail .panic) env fresh
  cases accepted <;>
    simpa [mutex_assert, NativeDrop.drop, NativeM.fail, discard_unit] using lifecycle

end Runtime.PayloadProperties
