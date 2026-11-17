module
public import Tables.Extraction.Funs
public section
open Aeneas Aeneas.Std
unseal RustM
namespace Tables.Properties
 theorem internal_replace (table : Tables.Extraction.OrderedCollections.Map) (key value : U64)
    (bounded : table.size ≤ 262144)
    (room : table.size < 262144 ∨ table.contains key.val) :
    experiment_analysis.experiment_core.ordered.replace_value table key value =
      .ok (table[key.val]?, table.insert key.val value) := by
  unfold experiment_analysis.experiment_core.ordered.replace_value Tables.Extraction.OrderedCollections.mapInsert
  rw [if_pos ⟨bounded, room⟩]
 theorem internal_claim (values : Tables.Extraction.OrderedCollections.Set) (key : U64)
    (bounded : values.size ≤ 262144)
    (room : values.size < 262144 ∨ values.contains key.val) :
    experiment_analysis.experiment_core.ordered.claim values key =
      .ok (!values.contains key.val, values.insert key.val) := by
  unfold experiment_analysis.experiment_core.ordered.claim Tables.Extraction.OrderedCollections.setInsert
  rw [if_pos ⟨bounded, room⟩]
 @[cbv_eval] theorem replace (key value replacement : U64) :
    experiment_analysis.table_replace key value replacement = .ok (some value) := by
  simp [experiment_analysis.table_replace, experiment_analysis.experiment_core.ordered.replace_value,
    Tables.Extraction.OrderedCollections.mapInsert, Tables.Extraction.OrderedCollections.mapNew, Std.TreeMap.size_insert]
 @[cbv_eval] theorem duplicate (key : U64) :
    experiment_analysis.set_insert_twice key = .ok (true, false, 1#u64) := by
  simp [experiment_analysis.set_insert_twice, experiment_analysis.experiment_core.ordered.claim,
    Tables.Extraction.OrderedCollections.setInsert, Tables.Extraction.OrderedCollections.setNew, Tables.Extraction.OrderedCollections.setLen, Std.TreeSet.size_insert, lift]
  scalar_tac
 @[cbv_eval] theorem stats (firstKey firstValue secondKey secondValue : U64) :
    experiment_analysis.table_stats firstKey firstValue secondKey secondValue =
      .ok (if firstKey.val = secondKey.val then (some firstValue, 1#u64) else (none, 2#u64)) := by
  by_cases same : firstKey.val = secondKey.val
  · have equal : firstKey = secondKey := by scalar_tac
    subst secondKey
    simp [experiment_analysis.table_stats, experiment_analysis.experiment_core.ordered.replace_value,
      Tables.Extraction.OrderedCollections.mapInsert, Tables.Extraction.OrderedCollections.mapNew,
      Tables.Extraction.OrderedCollections.mapLen, Std.TreeMap.size_insert, lift]
    scalar_tac
  · simp [experiment_analysis.table_stats, experiment_analysis.experiment_core.ordered.replace_value,
      Tables.Extraction.OrderedCollections.mapInsert, Tables.Extraction.OrderedCollections.mapNew,
      Tables.Extraction.OrderedCollections.mapLen, Std.TreeMap.size_insert,
      Std.TreeMap.getElem?_insert, same, Ne.symm same, lift]
    scalar_tac
theorem borrow_identity (T : Type) (value : T) :
    experiment_analysis.core.borrow.Borrow.Blanket.borrow value = .ok value := by rfl

theorem internal_peek (table : Tables.Extraction.OrderedCollections.Map) (key : U64)
    (bounded : table.size ≤ 262144) :
    experiment_analysis.experiment_core.ordered.peek table key = .ok table[key.val]? := by
  cases lookup : table[key.val]? <;>
    simp [experiment_analysis.experiment_core.ordered.peek,
      Tables.Extraction.OrderedCollections.mapGet, bounded, lookup] <;> rfl

theorem internal_take (table : Tables.Extraction.OrderedCollections.Map) (key : U64)
    (bounded : table.size ≤ 262144) :
    experiment_analysis.experiment_core.ordered.take table key =
      .ok (table[key.val]?, table.erase key.val) := by
  simp [experiment_analysis.experiment_core.ordered.take, Tables.Extraction.OrderedCollections.mapRemove, bounded]

theorem internal_contains (values : Tables.Extraction.OrderedCollections.Set) (key : U64)
    (bounded : values.size ≤ 262144) :
    experiment_analysis.experiment_core.ordered.contains values key = .ok (values.contains key.val) := by
  simp [experiment_analysis.experiment_core.ordered.contains, Tables.Extraction.OrderedCollections.setContains, bounded]

theorem internal_release (values : Tables.Extraction.OrderedCollections.Set) (key : U64)
    (bounded : values.size ≤ 262144) :
    experiment_analysis.experiment_core.ordered.release values key =
      .ok (values.contains key.val, values.erase key.val) := by
  simp [experiment_analysis.experiment_core.ordered.release, Tables.Extraction.OrderedCollections.setRemove, bounded]

theorem take_preserves_other (table : Tables.Extraction.OrderedCollections.Map) (key other : U64)
    (bounded : table.size ≤ 262144) (different : other.val ≠ key.val) :
    ∃ previous remaining,
      experiment_analysis.experiment_core.ordered.take table key = .ok (previous, remaining) ∧
      remaining[other.val]? = table[other.val]? := by
  refine ⟨table[key.val]?, table.erase key.val, internal_take table key bounded, ?_⟩
  simp [Std.TreeMap.getElem?_erase, Ne.symm different]

theorem release_preserves_other (values : Tables.Extraction.OrderedCollections.Set) (key other : U64)
    (bounded : values.size ≤ 262144) (different : other.val ≠ key.val) :
    ∃ previous remaining,
      experiment_analysis.experiment_core.ordered.release values key = .ok (previous, remaining) ∧
      remaining.contains other.val = values.contains other.val := by
  refine ⟨values.contains key.val, values.erase key.val, internal_release values key bounded, ?_⟩
  simp [Std.TreeSet.contains_erase, Ne.symm different]

@[cbv_eval] theorem take_once (key value query : U64) :
    experiment_analysis.table_take key value query =
      .ok (if key.val = query.val then (some value, some value, none, 0#u64)
        else (none, none, none, 1#u64)) := by
  by_cases same : key.val = query.val
  · have equal : key = query := by scalar_tac
    subst query
    simp [experiment_analysis.table_take, experiment_analysis.experiment_core.ordered.replace_value,
      internal_peek, internal_take, Tables.Extraction.OrderedCollections.mapInsert,
      Tables.Extraction.OrderedCollections.mapNew, Tables.Extraction.OrderedCollections.mapLen,
      Std.TreeMap.size_insert, Std.TreeMap.size_erase, lift]
    scalar_tac
  · simp [experiment_analysis.table_take, experiment_analysis.experiment_core.ordered.replace_value,
      internal_peek, internal_take, Tables.Extraction.OrderedCollections.mapInsert,
      Tables.Extraction.OrderedCollections.mapNew, Tables.Extraction.OrderedCollections.mapLen,
      Std.TreeMap.size_insert, Std.TreeMap.size_erase, same, lift]
    scalar_tac

@[cbv_eval] theorem release_once (key query : U64) :
    experiment_analysis.set_release key query =
      .ok (if key.val = query.val then (true, true, false, false, 0#u64)
        else (false, false, false, false, 1#u64)) := by
  by_cases same : key.val = query.val
  · have equal : key = query := by scalar_tac
    subst query
    simp [experiment_analysis.set_release, experiment_analysis.experiment_core.ordered.claim,
      internal_contains, internal_release, Tables.Extraction.OrderedCollections.setInsert,
      Tables.Extraction.OrderedCollections.setNew, Tables.Extraction.OrderedCollections.setLen,
      Std.TreeSet.size_insert, Std.TreeSet.size_erase, lift]
    scalar_tac
  · simp [experiment_analysis.set_release, experiment_analysis.experiment_core.ordered.claim,
      internal_contains, internal_release, Tables.Extraction.OrderedCollections.setInsert,
      Tables.Extraction.OrderedCollections.setNew, Tables.Extraction.OrderedCollections.setLen,
      Std.TreeSet.size_insert, Std.TreeSet.size_erase, same, lift]
    scalar_tac
end Tables.Properties
