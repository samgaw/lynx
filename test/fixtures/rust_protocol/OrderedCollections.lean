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
end Tables.Properties
