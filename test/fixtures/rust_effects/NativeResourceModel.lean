module
public import Resource.NativeRuntime
public section
open Lynx

namespace Resource.ModelProperties

/-- Model theorem only: extracted ResourceArc admission is checked separately. -/
theorem retained_payload (value : Bool) (env : Environment)
    (registered : NativeResourceArc.typeName Bool ∈ env.nativeResourceTypes)
    (empty : env.nativeHeap = []) :
    (do
      let first ← NativeResourceArc.new value
      let retained ← NativeResourceArc.clone first
      NativeResourceArc.release first
      let observed ← NativeResourceArc.deref retained
      NativeResourceArc.release retained
      Result.ok observed) env =
        (.ok value, { env with refCounter := env.refCounter + 3 }) := by
  exact NativeResourceArc.clone_release_cycle value env registered empty

theorem absent_registration (value : Bool) (env : Environment)
    (absent : NativeResourceArc.typeName Bool ∉ env.nativeResourceTypes) :
    NativeResourceArc.new value env = (.error (.error (.atom "rust_panicked")), env) := by
  exact NativeResourceArc.new_unregistered value env absent

theorem consumed_release (handle : NativeResourceArc Bool) (env : Environment)
    (absent : env.nativeHeap.filter (fun cell => cell.1 == handle.token) = []) :
    NativeResourceArc.release handle env = (.error .exhausted, env) := by
  exact NativeResourceArc.release_missing handle env absent

theorem forged_count (handle : NativeResourceArc Bool) (value : Bool) (env : Environment)
    (distinct : handle.id ≠ handle.token)
    (stored : env.nativeHeap = [
      (handle.token, NativeResourceArc.handleType Bool, .reference handle.id),
      (handle.id, NativeResourceArc.typeName Bool,
        .tuple #[.integer 2, NativeCodec.encode value])]) :
    NativeResourceArc.deref handle env = (.error .exhausted, env) := by
  exact NativeResourceArc.deref_inconsistent_count handle value env distinct stored

end Resource.ModelProperties
