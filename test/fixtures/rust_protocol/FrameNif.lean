module
public import Consume.SuffixProperties
public import Consume.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace Consume.FrameProperties

private theorem widen (value : Usize) : (UScalar.cast .U64 value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]


@[expose] def packet : Slice U8 := .from [76#u8,89#u8,78#u8,88#u8,0#u8,255#u8,13#u8,10#u8] (by scalar_tac)
@[expose] def marker : Slice U8 := .from [76#u8,89#u8,78#u8,88#u8,13#u8,10#u8] (by scalar_tac)
@[expose] def wrong : Slice U8 := .from [76#u8,89#u8,78#u8,88#u8,13#u8,10#u8,0#u8] (by scalar_tac)

theorem frame_bytes (input : ByteArray) : __FRAME__ input = (do
    let bytes ← Lynx.Rustler.binaryAsSlice input
    pure ((Consume.Properties.frame bytes).map
      (fun payload => UScalar.cast .U64 (Slice.len payload)))) := by
  simp only [__FRAME__, Consume.Properties.frame_length_bytes]
  rfl

theorem payload : __FRAME__ ⟨#[76,89,78,88,0,255,13,10]⟩ = RustM.ok (some 2#u64) := by
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[76,89,78,88,0,255,13,10]⟩ = RustM.ok packet := by
    have unsigned : 8 ≤ Usize.max := by scalar_tac
    have signed : (⟨#[76,89,78,88,0,255,13,10]⟩ : ByteArray).size ≤ Isize.max.toNat := by
      change 8 ≤ Isize.max.toNat
      scalar_tac
    simp [Lynx.Rustler.binaryAsSlice, packet, unsigned, signed]
    rfl
  simp [__FRAME__, decoded, Consume.Properties.frame_length_bytes, Consume.Properties.frame, Consume.Properties.tail, Consume.Properties.head, Consume.Properties.magic, packet]
  apply UScalar.eq_of_val_eq
  simp [widen, Slice.len, Consume.Properties.tail, Consume.Properties.head, packet]

theorem empty : __FRAME__ ⟨#[76,89,78,88,13,10]⟩ = RustM.ok (some 0#u64) := by
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[76,89,78,88,13,10]⟩ = RustM.ok marker := by
    have unsigned : 6 ≤ Usize.max := by scalar_tac
    have signed : (⟨#[76,89,78,88,13,10]⟩ : ByteArray).size ≤ Isize.max.toNat := by
      change 6 ≤ Isize.max.toNat
      scalar_tac
    simp [Lynx.Rustler.binaryAsSlice, marker, unsigned, signed]
    rfl
  simp [__FRAME__, decoded, Consume.Properties.frame_length_bytes, Consume.Properties.frame, Consume.Properties.tail, Consume.Properties.head, Consume.Properties.magic, marker]
  apply UScalar.eq_of_val_eq
  simp [widen, Slice.len, Consume.Properties.tail, Consume.Properties.head, marker]

theorem trailing : __FRAME__ ⟨#[76,89,78,88,13,10,0]⟩ = RustM.ok none := by
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[76,89,78,88,13,10,0]⟩ = RustM.ok wrong := by
    have unsigned : 7 ≤ Usize.max := by scalar_tac
    have signed : (⟨#[76,89,78,88,13,10,0]⟩ : ByteArray).size ≤ Isize.max.toNat := by
      change 7 ≤ Isize.max.toNat
      scalar_tac
    simp [Lynx.Rustler.binaryAsSlice, wrong, unsigned, signed]
    rfl
  simp [__FRAME__, decoded, Consume.Properties.frame_length_bytes, Consume.Properties.frame, Consume.Properties.tail, Consume.Properties.head, Consume.Properties.magic, wrong]


theorem comparator_panic : __SUFFIX_PANIC__ = RustM.fail .panic := by
  simp [__SUFFIX_PANIC__, Consume.Properties.suffix_panic]

end Consume.FrameProperties
