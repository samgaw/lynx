module
public import Buffer.Properties
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Buffer.CopyProperties
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem append_eq (output : alloc.vec.Vec U8) (input : Slice U8)
    (bound : output.val.length + input.val.length ≤ 262144) :
    atomic_core.append_bytes output input =
      NativeM.ok (alloc.vec.Vec.from (output.val ++ input.val) (by scalar_tac)) := by
  rw [atomic_core.append_bytes, Buffer.Extraction.VectorModel.extend_bytes_eq,
    dite_eq_left bound]
  rfl

theorem append_preserves_prefix (output : alloc.vec.Vec U8) (input : Slice U8)
    (bound : output.val.length + input.val.length ≤ 262144) :
    ∃ updated, atomic_core.append_bytes output input = NativeM.ok updated ∧
      updated.val = output.val ++ input.val := by
  exact ⟨_, append_eq output input bound, alloc.vec.Vec.from_val _ _⟩

theorem copy_bytes_eq (input : Slice U8) (bound : input.val.length ≤ 262144) :
    atomic_analysis.copy_bytes input =
      NativeM.ok (alloc.vec.Vec.from input.val (by scalar_tac)) := by
  simp only [atomic_analysis.copy_bytes, monadLift_self]
  rw [append_eq _ input (by simpa [alloc.vec.Vec.new] using bound)]
  rfl

theorem facade_view (input : Rustler.Binary) (view : Slice U8)
    (viewReturned : Rustler.binaryAsSlice input = RustM.ok view)
    (bound : view.val.length ≤ 262144) :
    __COPY__ input = NativeResourceArc.newOwned
      (⟨alloc.vec.Vec.from view.val (by scalar_tac)⟩ : ByteBuffer) := by
  simp [__COPY__, viewReturned, copy_bytes_eq view bound, NativeM.lift, NativeM.ok]

theorem facade_bytes (input : Rustler.Binary) (bound : input.size ≤ 262144) :
    ∃ payload, __COPY__ input = NativeResourceArc.newOwned payload ∧
      payload.bytes.val = input.data.toList.map (fun byte => (⟨byte.toBitVec⟩ : U8)) := by
  have unsignedBound : input.size ≤ Usize.max := by scalar_tac
  have signedBound : input.size ≤ Isize.max.toNat := by scalar_tac
  have viewReturned : Rustler.binaryAsSlice input = RustM.ok
      (Slice.from (input.data.toList.map (fun byte => (⟨byte.toBitVec⟩ : U8))) (by simpa using unsignedBound)) := by
    simp [Rustler.binaryAsSlice, unsignedBound, signedBound]
  rw [facade_view input _ viewReturned (by simpa using bound)]
  exact ⟨_, rfl, by simp⟩
-- This symbolic observation must use the proved storage inverse rather than
-- evaluate a dependent list conversion for every element.
private theorem indexed_storage_inverse (values : List U8) (bound : values.length ≤ Usize.max) :
    (Slice.from values bound).val = values := by
  cbv

end Buffer.CopyProperties
