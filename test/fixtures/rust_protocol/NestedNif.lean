module
public import NestedNative.Cases
public import NestedNative.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace NestedNative.NativeProperties

theorem facade_bounded (input : ByteArray) (bytes : Slice U8) (depth : U8) (nodes : U16)
    (decoded : Lynx.Rustler.binaryAsSlice input = RustM.ok bytes) :
    ∃ result, __FACADE__ input depth nodes = RustM.ok result ∧
      (∀ count, result = some count → 0 < count.val ∧ count.val ≤ nodes.val) := by
  obtain ⟨result, computed, facts⟩ := NestedNative.Properties.document_total bytes depth nodes
  exact ⟨result, by simp [__FACADE__, decoded, computed], facts⟩

theorem facade_siblings :
    __FACADE__ ⟨#[1,0,8,0,0,0,2,0,2,195,169]⟩ (⟨2#8⟩ : U8) (⟨3#16⟩ : U16) = RustM.ok (some 3#u16) := by
  change __FACADE__ ⟨#[1,0,8,0,0,0,2,0,2,195,169]⟩ 2#u8 3#u16 = _
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[1,0,8,0,0,0,2,0,2,195,169]⟩ =
      RustM.ok NestedNative.Cases.packet := by
    have unsigned : 11 ≤ Usize.max := by scalar_tac
    have signed : (⟨#[1,0,8,0,0,0,2,0,2,195,169]⟩ : ByteArray).size ≤ Isize.max.toNat := by
      change 11 ≤ Isize.max.toNat
      scalar_tac
    simp [Lynx.Rustler.binaryAsSlice, unsigned, signed, NestedNative.Cases.packet]
    rfl
  simp [__FACADE__, decoded, NestedNative.Cases.document_siblings]

end NestedNative.NativeProperties
