module
public import Aeneas
public import Std.Data.TreeMap
public import Std.Data.TreeSet
public section
open Aeneas Aeneas.Std
unseal RustM
namespace __PREFIX__.OrderedCollections
abbrev Map := Std.TreeMap Nat U64
abbrev Set := Std.TreeSet Nat
@[expose] def mapNew : Map := {}
@[expose] def setNew : Set := {}
@[expose] def mapInsert (table : Map) (key value : U64) : RustM (Option U64 × Map) :=
  if table.size ≤ 262144 ∧ (table.size < 262144 ∨ table.contains key.val) then
    .ok (table[key.val]?, table.insert key.val value)
  else .fail .undef
@[expose] def setInsert (values : Set) (key : U64) : RustM (Bool × Set) :=
  if values.size ≤ 262144 ∧ (values.size < 262144 ∨ values.contains key.val) then
    .ok (!values.contains key.val, values.insert key.val)
  else .fail .undef
@[expose] def setLen (values : Set) : RustM Usize :=
  if bounded : values.size ≤ 262144 then
    .ok (Usize.ofNatCore values.size (by scalar_tac))
  else .fail .undef
@[expose] def mapLen (table : Map) : RustM Usize :=
  if bounded : table.size ≤ 262144 then
    .ok (Usize.ofNatCore table.size (by scalar_tac))
  else .fail .undef
@[expose] def mapGet (table : Map) (key : U64) : RustM (Option U64) :=
  if table.size ≤ 262144 then .ok table[key.val]? else .fail .undef
@[expose] def mapRemove (table : Map) (key : U64) : RustM (Option U64 × Map) :=
  if table.size ≤ 262144 then .ok (table[key.val]?, table.erase key.val) else .fail .undef
@[expose] def setContains (values : Set) (key : U64) : RustM Bool :=
  if values.size ≤ 262144 then .ok (values.contains key.val) else .fail .undef
@[expose] def setRemove (values : Set) (key : U64) : RustM (Bool × Set) :=
  if values.size ≤ 262144 then .ok (values.contains key.val, values.erase key.val) else .fail .undef
theorem mapGet_cutoff (table : Map) (key : U64) (outside : 262144 < table.size) :
    mapGet table key = .fail .undef := by
  simp [mapGet, Nat.not_le_of_gt outside]
theorem mapRemove_cutoff (table : Map) (key : U64) (outside : 262144 < table.size) :
    mapRemove table key = .fail .undef := by
  simp [mapRemove, Nat.not_le_of_gt outside]
theorem setContains_cutoff (values : Set) (key : U64) (outside : 262144 < values.size) :
    setContains values key = .fail .undef := by
  simp [setContains, Nat.not_le_of_gt outside]
theorem setRemove_cutoff (values : Set) (key : U64) (outside : 262144 < values.size) :
    setRemove values key = .fail .undef := by
  simp [setRemove, Nat.not_le_of_gt outside]
theorem mapInsert_cutoff (table : Map) (key value : U64) (outside : 262144 < table.size) :
    mapInsert table key value = .fail .undef := by
  simp [mapInsert, Nat.not_le_of_gt outside]
theorem setInsert_cutoff (values : Set) (key : U64) (outside : 262144 < values.size) :
    setInsert values key = .fail .undef := by
  simp [setInsert, Nat.not_le_of_gt outside]
theorem mapInsert_replace_at_capacity (table : Map) (key value : U64)
    (full : table.size = 262144) (present : table.contains key.val = true) :
    mapInsert table key value = .ok (table[key.val]?, table.insert key.val value) := by
  unfold mapInsert
  rw [if_pos ⟨by omega, Or.inr present⟩]
end __PREFIX__.OrderedCollections
