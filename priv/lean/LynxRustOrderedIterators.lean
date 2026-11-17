module
public import __PREFIX__.OrderedCollectionsModel
public section
open Aeneas Aeneas.Std
unseal RustM
namespace __PREFIX__.OrderedIterators
open __PREFIX__.OrderedCollections
abbrev MapIterator := List (U64 × U64)
abbrev SetIterator := List U64
@[expose] def keyScalar (key : Nat) : U64 := U64.ofNatCore (key % 2^64) (by scalar_tac)
@[simp, cbv_eval] theorem keyScalar_key (key : U64) : keyScalar key.val = key := by
  apply UScalar.eq_of_val_eq
  change key.val % 2^64 = key.val
  exact Nat.mod_eq_of_lt (by scalar_tac)
@[expose] def mapIntoIter (table : Map) : RustM MapIterator :=
  if table.size ≤ 262144 ∧ table.toList.all (fun entry => decide (entry.1 < 2^64)) then
    .ok (table.toList.map (fun entry => (keyScalar entry.1, entry.2))) else .fail .undef
@[expose] def setIntoIter (values : Set) : RustM SetIterator :=
  if values.size ≤ 262144 ∧ values.toList.all (fun key => decide (key < 2^64)) then
    .ok (values.toList.map keyScalar) else .fail .undef
@[expose] def mapNext (remaining : MapIterator) : RustM (Option (U64 × U64) × MapIterator) :=
  if remaining.length ≤ 262144 then
    match remaining with
    | [] => .ok (none, [])
    | pair :: tail => .ok (some pair, tail)
  else .fail .undef
@[expose] def setNext (remaining : SetIterator) : RustM (Option U64 × SetIterator) :=
  if remaining.length ≤ 262144 then
    match remaining with
    | [] => .ok (none, [])
    | key :: tail =>
      .ok (some key, tail)
  else .fail .undef
theorem mapNext_cutoff (remaining : MapIterator) (outside : 262144 < remaining.length) :
    mapNext remaining = .fail .undef := by
  simp [mapNext, Nat.not_le_of_gt outside]
theorem mapNext_exhausted : mapNext [] = .ok (none, []) := by rfl
theorem mapIntoIter_cutoff (table : Map) (outside : 262144 < table.size) :
    mapIntoIter table = .fail .undef := by
  simp [mapIntoIter, Nat.not_le_of_gt outside]
theorem mapNext_progress (before after : MapIterator) (value : U64 × U64)
    (step : mapNext before = .ok (some value, after)) : after.length < before.length := by
  cases before with
  | nil => simp [mapNext] at step
  | cons head tail =>
    by_cases bounded : tail.length < 262144
    · simp [mapNext, bounded] at step
      rcases step with ⟨_, equal⟩
      subst after
      simp
    · simp [mapNext, bounded] at step
theorem setNext_cutoff (remaining : SetIterator) (outside : 262144 < remaining.length) :
    setNext remaining = .fail .undef := by
  simp [setNext, Nat.not_le_of_gt outside]
theorem setNext_exhausted : setNext [] = .ok (none, []) := by rfl
theorem setIntoIter_cutoff (values : Set) (outside : 262144 < values.size) :
    setIntoIter values = .fail .undef := by
  simp [setIntoIter, Nat.not_le_of_gt outside]
theorem setNext_progress (before after : SetIterator) (value : U64)
    (step : setNext before = .ok (some value, after)) : after.length < before.length := by
  cases before with
  | nil => simp [setNext] at step
  | cons head tail =>
    by_cases bounded : tail.length < 262144
    · simp [setNext, bounded] at step
      rcases step with ⟨_, equal⟩
      subst after
      simp
    · simp [setNext, bounded] at step
end __PREFIX__.OrderedIterators
