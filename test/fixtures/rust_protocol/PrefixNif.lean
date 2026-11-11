module
public import Prefix.Properties
public import Prefix.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace Prefix.NativeProperties

theorem marker_exact : __RECOGNIZE__ ⟨#[76,89,78,88]⟩ = RustM.ok true := by
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[76,89,78,88]⟩ = RustM.ok Prefix.Properties.marker := by
    have unsigned : 4 ≤ Usize.max := by scalar_tac
    have signed : (⟨#[76,89,78,88]⟩ : ByteArray).size ≤ Isize.max.toNat := by
      change 4 ≤ Isize.max.toNat
      scalar_tac
    simp [Lynx.Rustler.binaryAsSlice, Prefix.Properties.marker, unsigned, signed]
    rfl
  simp [__RECOGNIZE__, decoded, Prefix.Properties.marker_exact]

theorem marker_payload : __RECOGNIZE__ ⟨#[76,89,78,88,0,255,128]⟩ = RustM.ok true := by
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[76,89,78,88,0,255,128]⟩ = RustM.ok Prefix.Properties.payload := by
    have unsigned : 7 ≤ Usize.max := by scalar_tac
    have signed : (⟨#[76,89,78,88,0,255,128]⟩ : ByteArray).size ≤ Isize.max.toNat := by
      change 7 ≤ Isize.max.toNat
      scalar_tac
    simp [Lynx.Rustler.binaryAsSlice, Prefix.Properties.payload, unsigned, signed]
    rfl
  simp [__RECOGNIZE__, decoded, Prefix.Properties.marker_payload]

theorem reject_short : __RECOGNIZE__ ⟨#[]⟩ = RustM.ok false := by
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[]⟩ = RustM.ok Prefix.Properties.empty := by
    simp [Lynx.Rustler.binaryAsSlice, Prefix.Properties.empty]
    rfl
  simp [__RECOGNIZE__, decoded, Prefix.Properties.reject_short]

theorem short_circuit : __CHECKED__ false = RustM.ok false := by
  simp [__CHECKED__, Prefix.Properties.short_circuit]

theorem comparator_panic : __CHECKED__ true = RustM.fail .panic := by
  simp [__CHECKED__, Prefix.Properties.comparator_panic]

end Prefix.NativeProperties
