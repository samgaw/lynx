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
      (.ok value, { env with nativeRefCounter := env.nativeRefCounter + 3 }) := by
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
      (.ok value, { env with nativeRefCounter := env.nativeRefCounter + 3 }) := by
  simpa [scalar_resource_scope, scalar_resource_cycle] using
    retained_value value env registered empty


/-- The actual extracted constructor and cross-crate reader preserve a payload
through independent VM and Rust ownership. The VM pin remains live after both
Rust owners are released; garbage collection is outside this property. -/
theorem vm_owned_roundtrip (value : U64) (env : Environment)
    (registered : NativeResourceArc.typeName ScalarResource ∈ env.nativeResourceTypes)
    (empty : env.nativeHeap = []) :
    (do
      let original ← scalar_resource_new value
      let term ← NativeResourceArc.encode original
      let again ← NativeResourceArc.encode original
      NativeResourceArc.release original
      let decoded ← NativeResourceArc.decode (α := ScalarResource) term
      let observed ← scalar_resource_read decoded
      NativeResourceArc.release decoded
      Result.ok (observed, term == again)) env =
      (.ok (value, true), { env with nativeRefCounter := env.nativeRefCounter + 5, nativeHeap := [
        (env.nativeRefCounter + 4, NativeResourceArc.termType ScalarResource,
          .tuple #[.nativeReference (env.nativeRefCounter + 1), .nativeReference (env.nativeRefCounter + 3)]),
        (env.nativeRefCounter + 3, NativeResourceArc.handleType ScalarResource,
          .nativeReference (env.nativeRefCounter + 1)),
        (env.nativeRefCounter + 1, NativeResourceArc.typeName ScalarResource,
          .tuple #[.integer 1, NativeCodec.encode (ScalarResource.mk (effects_core.Counter.mk value))])] }) := by
  have cycle := NativeResourceArc.vm_roundtrip_next
    (ScalarResource.mk (effects_core.Counter.mk value))
    (fun resource same => Result.ok (resource.counter.value, same)) env registered empty
  simpa [scalar_resource_new, resource_reader, bind_assoc, NativeM.ok] using cycle

end Resource.Properties
