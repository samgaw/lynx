module
public import ByteVecNative.Core
public import ByteVecNative.RustlerBridge
public section
open Aeneas Aeneas.Std experiment_nif
namespace ByteVecNative.Properties

theorem facade (input : alloc.vec.Vec U8) (value : U8) :
    __FACADE__ input value =
      RustM.ok (!input.val.isEmpty, ⟨input.slice.set 0#usize value⟩) :=
  ByteVecNative.Core.composition input value

theorem facade_empty (value : U8) :
    __FACADE__ (alloc.vec.Vec.new U8) value =
      RustM.ok (false, alloc.vec.Vec.new U8) :=
  ByteVecNative.Core.empty_unchanged _ value (by simp [alloc.vec.Vec.new])

@[expose] def sample_input : alloc.vec.Vec U8 :=
  .from [1#u8, 2#u8, 3#u8] (by scalar_tac)
@[expose] def sample_output : alloc.vec.Vec U8 :=
  .from [9#u8, 2#u8, 3#u8] (by scalar_tac)

theorem decode_sample :
    Lynx.Rustler.decodeByteVec (Lynx.Term.list [.integer 1, .integer 2, .integer 3]) =
      .ok sample_input := by
  simpa [sample_input, Lynx.Rustler.encodeUnsigned] using
    Lynx.Rustler.decodeByteVec_list [1#u8, 2#u8, 3#u8]
      (by simp [Lynx.Rustler.byteVecLimit]) (by scalar_tac)

theorem decode_empty : Lynx.Rustler.decodeByteVec .nil = .ok (alloc.vec.Vec.new U8) := by
  simpa [alloc.vec.Vec.new] using
    Lynx.Rustler.decodeByteVec_list [] (by simp [Lynx.Rustler.byteVecLimit]) (by scalar_tac)

theorem facade_sample : __FACADE__ sample_input 9#u8 = .ok (true, sample_output) := by
  rw [facade]
  simp [sample_input, sample_output, alloc.vec.Vec.val, alloc.vec.Vec.from,
    Slice.set, Slice.setAtNat]

theorem encode_sample : Lynx.Rustler.encodeByteVec sample_output =
    .ok (Lynx.Term.list [.integer 9, .integer 2, .integer 3]) := by
  simp [Lynx.Rustler.encodeByteVec, sample_output, Lynx.Rustler.byteVecLimit,
    Lynx.Rustler.encodeUnsigned]

theorem encode_empty : Lynx.Rustler.encodeByteVec (alloc.vec.Vec.new U8) = .ok .nil := by
  simp [Lynx.Rustler.encodeByteVec, alloc.vec.Vec.new, Lynx.Rustler.byteVecLimit]

@[expose] def narrow_input : alloc.vec.Vec U8 := .from [0#u8, 255#u8] (by scalar_tac)
@[expose] def narrow_output : alloc.vec.Vec U8 := .from [9#u8, 255#u8] (by scalar_tac)

theorem decode_narrow :
    Lynx.Rustler.decodeByteVec (Lynx.Term.list [.integer 256, .integer 4294967295]) =
      .ok narrow_input := by
  unfold narrow_input
  apply Lynx.Rustler.decodeByteVec_values
  · exact .cons (by simp [Lynx.Rustler.decodeUnsigned]; rfl)
      (.cons (by simp [Lynx.Rustler.decodeUnsigned]; rfl) .nil)
  · simp [Lynx.Rustler.byteVecLimit]
  · scalar_tac

theorem facade_narrow : __FACADE__ narrow_input 9#u8 = .ok (true, narrow_output) := by
  rw [facade]
  simp [narrow_input, narrow_output, alloc.vec.Vec.val, alloc.vec.Vec.from,
    Slice.set, Slice.setAtNat]

theorem encode_narrow : Lynx.Rustler.encodeByteVec narrow_output =
    .ok (Lynx.Term.list [.integer 9, .integer 255]) := by
  simp [Lynx.Rustler.encodeByteVec, narrow_output, Lynx.Rustler.byteVecLimit,
    Lynx.Rustler.encodeUnsigned]

end ByteVecNative.Properties
