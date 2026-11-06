module
public import Resource.Facade.Funs
public import Resource.RustlerBridge
public import Lynx.Rustler
public section
open Lynx Aeneas Aeneas.Std effects_native
namespace Resource.Properties

theorem reader (counter : effects_core.Counter) : effects_core.counter_value counter = .ok counter.value := rfl

theorem resource_reader (resource : NativeResourceArc ScalarResource) :
    scalar_resource_read resource = (do let contents ← NativeResourceArc.deref resource; Result.ok contents.counter.value) := by
  simp [scalar_resource_read, reader, NativeM.ok]

theorem facade_continuation {β : Type} (value : U64) (next : Term → Result β)
    (env : Environment) (registered : NativeResourceArc.typeName ScalarResource ∈ env.nativeResourceTypes)
    (empty : env.nativeHeap = []) :
    (Rustler.executeNative (__NIF__ value) Rustler.encodeUnsigned >>= next) env =
      next (.integer value.val) { env with refCounter := env.refCounter + 3 } := by
  have cycle := NativeResourceArc.clone_release_cycle_handled_next
    (ScalarResource.mk (effects_core.Counter.mk value))
    (fun resource => Result.ok (Rustler.encodeUnsigned resource.counter.value))
    (fun error => match error with
      | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
      | _ => Result.error .exhausted)
    next env registered empty
  convert cycle using 1 <;> simp [__NIF__,
    scalar_resource_cycle, scalar_resource_new, scalar_resource_clone,
    resource_reader, NativeDrop.drop, NativeM.ok, Rustler.executeNative, bind_assoc,
    Rustler.encodeUnsigned, Result.handle]
  all_goals rfl
end Resource.Properties
