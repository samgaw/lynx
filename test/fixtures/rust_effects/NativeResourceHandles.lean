module
public import Handles.Extraction.Funs
public import Handles.RustlerBridge
public import Lynx.Rustler
public section
open Lynx Aeneas Aeneas.Std effects_native
namespace Handles.Properties

theorem reader (counter : effects_core.Counter) :
    effects_core.counter_value counter = Result.ok counter.value := rfl

theorem resource_reader (resource : NativeResourceArc ScalarResource) :
    scalar_resource_read resource = (do
      let contents ← NativeResourceArc.deref resource
      Result.ok contents.counter.value) := by
  simp [scalar_resource_read, reader]

theorem checked_reader (resource : NativeResourceArc ScalarResource) :
    __CHECKED__ resource true = __READ__ resource := by
  simp [__CHECKED__, __READ__]

theorem checked_disabled (resource : NativeResourceArc ScalarResource) :
    __CHECKED__ resource false = (do NativeResourceArc.release resource; NativeM.ok 0#u64) := by
  simp [__CHECKED__, NativeDrop.drop, NativeM.ok]

theorem create_continuation {β : Type} (value : U64) (next : Term → Result β)
    (env : Environment) (registered : NativeResourceArc.typeName ScalarResource ∈ env.nativeResourceTypes)
    (empty : env.nativeHeap = []) :
    (Rustler.executeNative (do
      let owner ← __CREATE__ value
      let term ← NativeResourceArc.encode owner
      NativeResourceArc.release owner
      Result.ok term) id >>= next) env =
    next (.reference (env.refCounter + 4)) {env with refCounter := env.refCounter + 4, nativeHeap := [
      (env.refCounter + 4, NativeResourceArc.termType ScalarResource,
        .tuple #[.reference (env.refCounter + 1), .reference (env.refCounter + 3)]),
      (env.refCounter + 3, NativeResourceArc.handleType ScalarResource, .reference (env.refCounter + 1)),
      (env.refCounter + 1, NativeResourceArc.typeName ScalarResource,
        .tuple #[.integer 1, NativeCodec.encode (ScalarResource.mk (effects_core.Counter.mk value))])] } := by
  have model := NativeResourceArc.new_encode_release_handled_next
    (ScalarResource.mk (effects_core.Counter.mk value))
    (fun error => match error with
      | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
      | _ => Result.error .exhausted)
    next env registered empty
  convert model using 1
  simp [__CREATE__, scalar_resource_new, Rustler.executeNative]
  all_goals rfl

theorem read_continuation {β : Type} (value : U64) (next : Term → Result β)
    (env : Environment) (id pin term : Nat)
    (ordered : id < pin ∧ pin < term ∧ term ≤ env.refCounter)
    (stored : env.nativeHeap = [
      (term, NativeResourceArc.termType ScalarResource, .tuple #[.reference id, .reference pin]),
      (pin, NativeResourceArc.handleType ScalarResource, .reference id),
      (id, NativeResourceArc.typeName ScalarResource,
        .tuple #[.integer 1, NativeCodec.encode (ScalarResource.mk (effects_core.Counter.mk value))])])
    (registered : NativeResourceArc.typeName ScalarResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (α := ScalarResource) (.reference term)
      let result ← Rustler.executeNative (__READ__ owner) Rustler.encodeUnsigned
      next result) env = next (.integer value.val) {env with refCounter := env.refCounter + 1} := by
  have model := NativeResourceArc.decode_read_release_handled_next
    (ScalarResource.mk (effects_core.Counter.mk value))
    (fun resource => Result.ok (Rustler.encodeUnsigned resource.counter.value))
    (fun error => match error with
      | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
      | _ => Result.error .exhausted)
    next env id pin term ordered stored registered
  convert model using 1 <;> simp [__READ__, resource_reader, NativeDrop.drop,
    NativeM.ok, Rustler.executeNative, Result.handle, bind_assoc, Rustler.encodeUnsigned]
  all_goals rfl
end Handles.Properties
