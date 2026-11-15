module
public import SharedBytes.Properties
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace SharedBytes.NifProperties

theorem create_contract :
    __NEW__ = (do
      let mutex ← NativeMutex.new (atomic_analysis.ReceiveState.mk (atomic_core.BufferState.mk (alloc.vec.Vec.new U8)))
      NativeResourceArc.newOwned (SharedBuffer.mk mutex)) := rfl

theorem append_contract (owner : NativeResourceArc SharedBuffer) (input : Rustler.Binary) :
    __APPEND__ owner input = (do
      let value ← NativeResourceArc.deref owner
      let bytes ← NativeM.fromRust (Rustler.binaryAsSlice input)
      let length ← atomic_analysis.append_state value.state bytes
      NativeResourceArc.releaseOwned owner
      .ok length) := by
  simp [__APPEND__, NativeOwnedDrop.drop, NativeM.ok]

theorem read_contract (owner : NativeResourceArc SharedBuffer) :
    __READ__ owner = (do
      let value ← NativeResourceArc.deref owner
      let result ← atomic_analysis.read_state value.state
      NativeResourceArc.releaseOwned owner
      .ok result) := by
  simp [__READ__, NativeOwnedDrop.drop, NativeM.ok]
-- The checked evaluator must preserve native failure distinctions without
-- expanding the coinductive foreign computation representation.
private theorem lifted_failures :
    NativeM.fromRust (RustM.fail .panic : RustM Unit) =
        Result.error (.error (.atom "rust_panicked")) ∧
      NativeM.fromRust (RustM.fail .undef : RustM Unit) = Result.error .exhausted ∧
      NativeM.fromRust (RustM.div : RustM Unit) = Result.error .exhausted ∧
      NativeM.fromRust (Aeneas.Std.bind (RustM.ok ()) fun _ => RustM.fail .panic : RustM Unit) =
        Result.error (.error (.atom "rust_panicked")) := by
  cbv

end SharedBytes.NifProperties
