module
public import Frames.Properties
public import Frames.RustlerBridge
public section
open Aeneas Aeneas.Std atomic_nif
namespace Frames.NifProperties

attribute [cbv_opaque] RustM.ok RustM.fail RustM.div Aeneas.Std.bind Slice.from
attribute [cbv_eval] Aeneas.Std.bind_ok Aeneas.Std.bind_fail Aeneas.Std.bind_div Slice.from_val

@[cbv_eval] private theorem widen64 (value : Usize) : UScalar.cast .U64 value =
    U64.ofNatCore value.val (by
      have bound := value.hmax
      cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits] <;> omega) := by
  apply UScalar.eq_of_val_eq
  have bound := value.hmax
  simp only [UScalar.cast_val_eq]
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
  all_goals omega

@[cbv_eval] private theorem widen16 (value : U16) : UScalar.cast .Usize value =
    Usize.ofNatCore value.val (by cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits] <;> scalar_tac) := by
  apply UScalar.eq_of_val_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalar.cast_val_eq, UScalarTy.numBits]
  all_goals scalar_tac

attribute [cbv_eval] Lynx.Rustler.execute_ok Lynx.Rustler.execute_panic
  Lynx.Rustler.execute_undef Lynx.Rustler.execute_div

theorem summary_contract (input : Lynx.Rustler.Binary) :
    __SUMMARY__ input = (do
      let bytes ← Lynx.Rustler.binaryAsSlice input
      atomic_analysis.frame_summary bytes) := rfl

theorem summary_empty : __SUMMARY__ ⟨#[]⟩ = RustM.ok (0#u8, 0#u64, 0#u64) := by
  cbv

theorem summary_frame : __SUMMARY__ ⟨#[1,0,2,128,255,1,0,0]⟩ =
    RustM.ok (2#u8, 5#u64, 3#u64) := by
  cbv
  all_goals
    rcases System.Platform.numBits_eq with bits | bits
    all_goals
      change (System.Platform.getNumBits PUnit.unit).1 = _ at bits
      iterate 5
        all_goals
          simp only [bits]
          cbv

theorem summary_truncated : __SUMMARY__ ⟨#[1,0,2,128]⟩ =
    RustM.ok (0#u8, 0#u64, 4#u64) := by
  cbv
  all_goals
    rcases System.Platform.numBits_eq with bits | bits
    all_goals
      change (System.Platform.getNumBits PUnit.unit).1 = _ at bits
      iterate 5
        all_goals
          simp only [bits]
          cbv

theorem summary_bad_version : __SUMMARY__ ⟨#[2,0,0]⟩ =
    RustM.ok (1#u8, 0#u64, 3#u64) := by
  cbv

theorem split_middle : __SPLIT__ ⟨#[0,128,255]⟩ 1#u16 = RustM.ok (1#u64, 2#u64) := by
  cbv

theorem split_empty : __SPLIT__ ⟨#[]⟩ 0#u16 = RustM.ok (0#u64, 0#u64) := by
  cbv

theorem split_panic : __SPLIT__ ⟨#[1]⟩ 2#u16 = RustM.fail .panic := by
  cbv

theorem split_zero : __SPLIT__ ⟨#[0,128,255]⟩ 0#u16 = RustM.ok (0#u64, 3#u64) := by
  cbv

theorem summary_zero : __SUMMARY__ ⟨#[1,0,0]⟩ = RustM.ok (2#u8, 3#u64, 0#u64) := by
  cbv
  all_goals
    rcases System.Platform.numBits_eq with bits | bits
    all_goals
      change (System.Platform.getNumBits PUnit.unit).1 = _ at bits
      iterate 5
        all_goals
          simp only [bits]
          cbv

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
set_option cbv.maxSteps 1000000 in
theorem summary_network :
    __SUMMARY__ ⟨#[1,1,0] ++ (Array.replicate 256 7 ++ #[1,0,0])⟩ =
      RustM.ok (2#u8, 259#u64, 3#u64) := by
  cbv
  all_goals
    rcases System.Platform.numBits_eq with bits | bits
    all_goals
      change (System.Platform.getNumBits PUnit.unit).1 = _ at bits
      iterate 5
        all_goals
          simp only [bits]
          cbv

private theorem distinct_failures :
    Lynx.Rustler.execute (RustM.fail .panic : RustM Unit) (fun _ => .atom "ok") =
        Except.error (.error (.atom "nif_panicked")) ∧
      Lynx.Rustler.execute (RustM.fail .undef : RustM Unit) (fun _ => .atom "ok") =
        Except.error .exhausted ∧
      Lynx.Rustler.execute (RustM.div : RustM Unit) (fun _ => .atom "ok") =
        Except.error .exhausted := by
  cbv
end Frames.NifProperties
