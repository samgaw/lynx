module
public import Indexed.WindowProperties
public import Indexed.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace Indexed.NativeProperties

private theorem widen8 (value : U8) : (UScalar.cast .Usize value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

private theorem widen64 (value : Usize) : (UScalar.cast .U64 value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

def input : Slice U8 := .from [0#u8,255#u8,128#u8] (by scalar_tac)

theorem facade (start stop : U8) :
    __FACADE__ ⟨#[0,255,128]⟩ start stop =
      experiment_nif.experiment_analysis.indexed_length input start stop := by
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[0,255,128]⟩ = RustM.ok input := by
    have unsigned : 3 ≤ Usize.max := by scalar_tac
    have signed : (⟨#[0,255,128]⟩ : ByteArray).size ≤ Isize.max.toNat := by
      change 3 ≤ Isize.max.toNat
      scalar_tac
    simp [Lynx.Rustler.binaryAsSlice, input, unsigned, signed]
    rfl
  simp [__FACADE__, decoded]

theorem success : __FACADE__ ⟨#[0,255,128]⟩ 1#u8 3#u8 = RustM.ok 2#u64 := by
  rw [facade]
  simp [experiment_nif.experiment_analysis.indexed_length,
    experiment_nif.experiment_analysis.indexed_window, Indexed.Properties.core_window,
    widen8, input, lift]
  apply UScalar.eq_of_val_eq
  simp [widen64, widen8, Slice.len, Indexed.Properties.expectedWindow, input, List.slice]

theorem reversed : __FACADE__ ⟨#[0,255,128]⟩ 3#u8 1#u8 = RustM.fail .panic := by
  rw [facade]
  simp [experiment_nif.experiment_analysis.indexed_length,
    experiment_nif.experiment_analysis.indexed_window, Indexed.Properties.core_window,
    widen8, lift]

theorem truncated : __FACADE__ ⟨#[0,255,128]⟩ 0#u8 4#u8 = RustM.fail .panic := by
  rw [facade]
  simp [experiment_nif.experiment_analysis.indexed_length,
    experiment_nif.experiment_analysis.indexed_window, Indexed.Properties.core_window,
    widen8, input, lift]

end Indexed.NativeProperties
