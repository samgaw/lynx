module
public import Consume.Properties
public import Consume.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace Consume.NativeProperties

private theorem widen (value : Usize) : (UScalar.cast .U64 value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

@[expose] def packet : Slice U8 := .from [76#u8,89#u8,78#u8,88#u8,0#u8,255#u8] (by scalar_tac)
@[expose] def marker : Slice U8 := .from [76#u8,89#u8,78#u8,88#u8] (by scalar_tac)
@[expose] def wrong : Slice U8 := .from [76#u8,89#u8,78#u8,89#u8] (by scalar_tac)

theorem facade_bytes (input : ByteArray) : __PAYLOAD__ input = (do
    let bytes ← Lynx.Rustler.binaryAsSlice input
    pure (if 4 ≤ bytes.val.length ∧ bytes.val.take 4 = Consume.Properties.magic
      then some (UScalar.cast .U64 (Slice.len (Consume.Properties.tail bytes 4))) else none)) := by
  simp only [__PAYLOAD__, Consume.Properties.length_bytes]
  rfl

theorem payload : __PAYLOAD__ ⟨#[76,89,78,88,0,255]⟩ = RustM.ok (some 2#u64) := by
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[76,89,78,88,0,255]⟩ = RustM.ok packet := by
    have unsigned : 6 ≤ Usize.max := by scalar_tac
    have signed : (⟨#[76,89,78,88,0,255]⟩ : ByteArray).size ≤ Isize.max.toNat := by
      change 6 ≤ Isize.max.toNat
      scalar_tac
    simp [Lynx.Rustler.binaryAsSlice, packet, unsigned, signed]
    rfl
  simp [__PAYLOAD__, decoded, Consume.Properties.length_bytes, Consume.Properties.magic, packet]
  apply UScalar.eq_of_val_eq
  simp [widen, Slice.len, Consume.Properties.tail, packet]

theorem exact_marker : __PAYLOAD__ ⟨#[76,89,78,88]⟩ = RustM.ok (some 0#u64) := by
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[76,89,78,88]⟩ = RustM.ok marker := by
    have unsigned : 4 ≤ Usize.max := by scalar_tac
    have signed : (⟨#[76,89,78,88]⟩ : ByteArray).size ≤ Isize.max.toNat := by
      change 4 ≤ Isize.max.toNat
      scalar_tac
    simp [Lynx.Rustler.binaryAsSlice, marker, unsigned, signed]
    rfl
  simp [__PAYLOAD__, decoded, Consume.Properties.length_bytes, Consume.Properties.magic, marker]
  apply UScalar.eq_of_val_eq
  simp [widen, Slice.len, Consume.Properties.tail, marker]

theorem mismatch : __PAYLOAD__ ⟨#[76,89,78,89]⟩ = RustM.ok none := by
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[76,89,78,89]⟩ = RustM.ok wrong := by
    have unsigned : 4 ≤ Usize.max := by scalar_tac
    have signed : (⟨#[76,89,78,89]⟩ : ByteArray).size ≤ Isize.max.toNat := by
      change 4 ≤ Isize.max.toNat
      scalar_tac
    simp [Lynx.Rustler.binaryAsSlice, wrong, unsigned, signed]
    rfl
  simp [__PAYLOAD__, decoded, Consume.Properties.length_bytes, Consume.Properties.magic, wrong]

theorem truncated : __PAYLOAD__ ⟨#[]⟩ = RustM.ok none := by
  have signed : (⟨#[]⟩ : ByteArray).size ≤ Isize.max.toNat := by
    change 0 ≤ _
    exact Nat.zero_le _
  simp [__PAYLOAD__, Lynx.Rustler.binaryAsSlice, signed, Consume.Properties.length_bytes]

theorem comparator_panic : __CHECKED__ = RustM.fail .panic := by
  simp [__CHECKED__, Consume.Properties.comparator_panic]

theorem recognition_order : __RECOGNIZE__ = RustM.ok false := by
  simp [__RECOGNIZE__, Consume.Properties.recognize_without_panic]

end Consume.NativeProperties
