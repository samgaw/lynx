module

public import Aeneas
-- Intentional implementation dependency: upstream keeps the arithmetic body private.
-- Clients use the public theorem below through ordinary generated-module imports.
import all Aeneas.Std.Scalar.SaturatingOps
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Scalar.CheckedOps.Mul

public section

open Aeneas Aeneas.Std Aeneas.Std.ScalarElab

namespace Lynx.Rust.Scalar

/-- Mathematical value of upstream unsigned saturating addition. This downstream
proof adds no arithmetic model and needs no modification of the Aeneas library. -/
@[simp, scalar_tac_simps]
theorem saturatingAdd_val_eq {ty : UScalarTy} (x y : UScalar ty) :
    (UScalar.saturating_add x y).val = min (UScalar.max ty) (x.val + y.val) := by
  simp only [UScalar.saturating_add, UScalar.val, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have positive : 0 < 2 ^ ty.numBits := Nat.two_pow_pos _
  have bound : UScalar.max ty < 2 ^ ty.numBits := by
    simp only [UScalar.max]
    omega
  exact lt_of_le_of_lt (Nat.min_le_left _ _) bound


-- Public specifications of upstream's generated fixed-width aliases.
uscalar @[simp, scalar_tac_simps]
theorem «%S».saturatingAdd_val_eq (x y : Aeneas.Std.«%S») :
    (Aeneas.Std.core.num.«%S».saturating_add x y).val =
      min (UScalar.max UScalarTy.«%S») (x.val + y.val) :=
  Lynx.Rust.Scalar.saturatingAdd_val_eq x y

/-- Integer-value specification of upstream's private checked-add alias. -/
theorem checkedAddI64_spec (x y : Aeneas.Std.I64) :
    match Aeneas.Std.I64.checked_add x y with
    | some z => Aeneas.Std.I64.min ≤ x.val + y.val ∧
        x.val + y.val ≤ Aeneas.Std.I64.max ∧ z.val = x.val + y.val
    | none => ¬ (Aeneas.Std.I64.min ≤ x.val + y.val ∧ x.val + y.val ≤ Aeneas.Std.I64.max) := by
  have spec := Aeneas.Std.I64.checked_add_bv_spec x y
  change (match Aeneas.Std.I64.checked_add x y with
    | some z => Aeneas.Std.I64.min ≤ x.val + y.val ∧
        x.val + y.val ≤ Aeneas.Std.I64.max ∧ z.val = x.val + y.val ∧
        Aeneas.Std.I64.bv z = Aeneas.Std.I64.bv x + Aeneas.Std.I64.bv y
    | none => ¬ (Aeneas.Std.I64.min ≤ x.val + y.val ∧ x.val + y.val ≤ Aeneas.Std.I64.max)) at spec
  cases result : Aeneas.Std.I64.checked_add x y with
  | none => simpa only [result] using spec
  | some z =>
    simp only [result] at spec ⊢
    exact ⟨spec.1, spec.2.1, spec.2.2.1⟩

/-- A kernel-proved evaluation rule for upstream's private checked-add alias.
The bounded signed result is retained; overflow returns none rather than wrapping. -/
@[cbv_eval] theorem checkedAddI64_eq (x y : I64) :
    I64.checked_add x y =
      if (-9223372036854775808 : Int) ≤ x.val + y.val ∧ x.val + y.val ≤ 9223372036854775807 then
        some (⟨BitVec.ofInt IScalarTy.I64.numBits (x.val + y.val)⟩ : I64)
      else none := by
  have spec := checkedAddI64_spec x y
  cases result : I64.checked_add x y with
  | none =>
    simp only [result, I64.min_eq, I64.max_eq] at spec
    simp [spec]
  | some value =>
    simp only [result, I64.min_eq, I64.max_eq] at spec
    rw [ite_eq_left ⟨spec.1, spec.2.1⟩, ← spec.2.2]
    simp only [IScalar.BitVec_ofInt_val]

/-- Exact reduction of upstream unsigned checked addition, without exposing its
private implementation to client proofs. Overflow is None, never wrapped success. -/
@[cbv_eval] theorem checkedAddU64_eq (x y : U64) :
    U64.checked_add x y =
      if x.val + y.val ≤ 18446744073709551615 then
        some (⟨BitVec.ofNat 64 (x.val + y.val)⟩ : U64)
      else none := by
  have spec := U64.checked_add_bv_spec x y
  cases result : U64.checked_add x y with
  | none =>
    simp only [result, U64.max_eq] at spec
    simp [Nat.not_le.mpr spec]
  | some value =>
    simp only [result, U64.max_eq] at spec
    rw [ite_eq_left spec.1, ← spec.2.1]
    simp only [U64.BitVec_ofNat_val]

/-- Integer-value specification of upstream's private checked-mul alias. -/
theorem checkedMulI64_spec (x y : Aeneas.Std.I64) :
    match Aeneas.Std.I64.checked_mul x y with
    | some z => Aeneas.Std.I64.min ≤ x.val * y.val ∧
        x.val * y.val ≤ Aeneas.Std.I64.max ∧ z.val = x.val * y.val
    | none => ¬ (Aeneas.Std.I64.min ≤ x.val * y.val ∧ x.val * y.val ≤ Aeneas.Std.I64.max) := by
  have spec := Aeneas.Std.I64.checked_mul_bv_spec x y
  change (match Aeneas.Std.I64.checked_mul x y with
    | some z => Aeneas.Std.I64.min ≤ x.val * y.val ∧
        x.val * y.val ≤ Aeneas.Std.I64.max ∧ z.val = x.val * y.val ∧
        Aeneas.Std.I64.bv z = Aeneas.Std.I64.bv x * Aeneas.Std.I64.bv y
    | none => ¬ (Aeneas.Std.I64.min ≤ x.val * y.val ∧ x.val * y.val ≤ Aeneas.Std.I64.max)) at spec
  cases result : Aeneas.Std.I64.checked_mul x y with
  | none => simpa only [result] using spec
  | some z =>
    simp only [result] at spec ⊢
    exact ⟨spec.1, spec.2.1, spec.2.2.1⟩

end Lynx.Rust.Scalar
