module
public import Resource.Extraction.Funs
public section
open Lynx Aeneas Aeneas.Std effects_native
namespace Resource.Properties

theorem counter_reader (counter : effects_core.Counter) :
    effects_core.counter_value counter = Result.ok counter.value := by
  rfl

theorem resource_reader (resource : NativeResourceArc ScalarResource) :
    scalar_resource_read resource = (do
      let contents ← NativeResourceArc.deref resource
      Result.ok contents.counter.value) := by
  simp [scalar_resource_read, counter_reader]

theorem retained_value (value : U64) (env : Environment)
    (registered : NativeResourceArc.typeName ScalarResource ∈ env.nativeResourceTypes)
    (empty : env.nativeHeap = []) :
    scalar_resource_cycle value env =
      (.ok value, { env with refCounter := env.refCounter + 3 }) := by
  have cycle := NativeResourceArc.clone_release_cycle_next
    (ScalarResource.mk (effects_core.Counter.mk value))
    (fun resource => Result.ok resource.counter.value) env registered empty
  simpa [scalar_resource_cycle, scalar_resource_new, scalar_resource_clone,
    resource_reader, NativeDrop.drop, NativeM.ok] using cycle

theorem unregistered_panics (value : U64) (env : Environment)
    (absent : NativeResourceArc.typeName ScalarResource ∉ env.nativeResourceTypes) :
    scalar_resource_cycle value env =
      (.error (.error (.atom "rust_panicked")), env) := by
  simp [scalar_resource_cycle, scalar_resource_new, NativeResourceArc.new,
    absent, NativeM.fail]

theorem scope_value (value : U64) (env : Environment)
    (registered : NativeResourceArc.typeName ScalarResource ∈ env.nativeResourceTypes)
    (empty : env.nativeHeap = []) :
    scalar_resource_scope value env =
      (.ok value, { env with refCounter := env.refCounter + 3 }) := by
  simpa [scalar_resource_scope, scalar_resource_cycle] using
    retained_value value env registered empty
end Resource.Properties
