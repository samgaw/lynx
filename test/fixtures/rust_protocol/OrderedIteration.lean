module
public import __PREFIX__.Extraction.Funs
public section
open Aeneas Aeneas.Std
unseal RustM
namespace __PREFIX__.Properties

@[expose] def entry (pair : U64 × U64) : __CORE__.Entry := { key := pair.1, value := pair.2 }

theorem entries_loop (remaining : __PREFIX__.Extraction.OrderedIterators.MapIterator)
    (output : alloc.vec.Vec __CORE__.Entry)
    (bounded : output.val.length + remaining.length ≤ 262144) :
    ∃ result, __CORE__.entries_loop remaining output = .ok result ∧
      result.val = output.val ++ remaining.map entry := by
  induction remaining generalizing output with
  | nil =>
    refine ⟨output, ?_, by simp⟩
    rw [__CORE__.entries_loop, loop.eq_1]
    simp [__CORE__.entries_loop.body, __PREFIX__.Extraction.OrderedIterators.mapNext]
  | cons pair tail ih =>
    rcases pair with ⟨key, value⟩
    let row : __CORE__.Entry := { key, value }
    have room : output.val.length + 1 ≤ U32.max := by simp at bounded; scalar_tac
    have grow : output.val.length < 262144 := by simp at bounded; omega
    let next := alloc.vec.Vec.from (output.val ++ [row]) (by simp; scalar_tac)
    have pushed : __PREFIX__.Extraction.VectorModel.push output row = .ok next := by
      rw [__PREFIX__.Extraction.VectorModel.push_within output row grow]
      simp [alloc.vec.Vec.push, room, next]
    have nextBound : next.val.length + tail.length ≤ 262144 := by
      simp [next]; simp at bounded; omega
    obtain ⟨result, returned, values⟩ := ih next nextBound
    refine ⟨result, ?_, by simpa [next, row, entry, List.append_assoc] using values⟩
    rw [__CORE__.entries_loop, loop.eq_1]
    have remainingBound : tail.length < 262144 := by simp at bounded; omega
    simp [__CORE__.entries_loop.body, __PREFIX__.Extraction.OrderedIterators.mapNext,
      remainingBound, pushed, row] at *
    exact returned

theorem members_loop (remaining : __PREFIX__.Extraction.OrderedIterators.SetIterator)
    (output : alloc.vec.Vec U64) (bounded : output.val.length + remaining.length ≤ 262144) :
    ∃ result, __CORE__.members_loop remaining output = .ok result ∧
      result.val = output.val ++ remaining := by
  induction remaining generalizing output with
  | nil =>
    refine ⟨output, ?_, by simp⟩
    rw [__CORE__.members_loop, loop.eq_1]
    simp [__CORE__.members_loop.body, __PREFIX__.Extraction.OrderedIterators.setNext]
  | cons key tail ih =>
    have room : output.val.length + 1 ≤ U32.max := by simp at bounded; scalar_tac
    have grow : output.val.length < 262144 := by simp at bounded; omega
    let next := alloc.vec.Vec.from (output.val ++ [key]) (by simp; scalar_tac)
    have pushed : __PREFIX__.Extraction.VectorModel.push output key = .ok next := by
      rw [__PREFIX__.Extraction.VectorModel.push_within output key grow]
      simp [alloc.vec.Vec.push, room, next]
    have nextBound : next.val.length + tail.length ≤ 262144 := by
      simp [next]; simp at bounded; omega
    obtain ⟨result, returned, values⟩ := ih next nextBound
    refine ⟨result, ?_, by simpa [next, List.append_assoc] using values⟩
    rw [__CORE__.members_loop, loop.eq_1]
    have remainingBound : tail.length < 262144 := by simp at bounded; omega
    simp [__CORE__.members_loop.body, __PREFIX__.Extraction.OrderedIterators.setNext,
      remainingBound, pushed]
    exact returned

@[cbv_eval] theorem entries_snapshot (table : __PREFIX__.Extraction.OrderedCollections.Map)
    (snapshot : __PREFIX__.Extraction.OrderedIterators.MapIterator)
    (decoded : __PREFIX__.Extraction.OrderedIterators.mapIntoIter table = .ok snapshot)
    (bounded : snapshot.length ≤ 262144) :
    __CORE__.entries table = .ok (alloc.vec.Vec.from (snapshot.map entry) (by simp; scalar_tac)) := by
  obtain ⟨result, returned, values⟩ := entries_loop snapshot (alloc.vec.Vec.new __CORE__.Entry) (by simpa [alloc.vec.Vec.new] using bounded)
  have same : result = alloc.vec.Vec.from (snapshot.map entry) (by simp; scalar_tac) := by
    apply alloc.vec.Vec.ext
    simpa [alloc.vec.Vec.new] using values
  simp [__CORE__.entries, decoded, returned, same]

@[cbv_eval] theorem members_snapshot (values : __PREFIX__.Extraction.OrderedCollections.Set)
    (snapshot : __PREFIX__.Extraction.OrderedIterators.SetIterator)
    (decoded : __PREFIX__.Extraction.OrderedIterators.setIntoIter values = .ok snapshot)
    (bounded : snapshot.length ≤ 262144) :
    __CORE__.members values = .ok (alloc.vec.Vec.from snapshot (by scalar_tac)) := by
  obtain ⟨result, returned, contents⟩ := members_loop snapshot (alloc.vec.Vec.new U64) (by simpa [alloc.vec.Vec.new] using bounded)
  have same : result = alloc.vec.Vec.from snapshot (by scalar_tac) := by
    apply alloc.vec.Vec.ext
    simpa [alloc.vec.Vec.new] using contents
  simp [__CORE__.members, decoded, returned, same]

theorem entries_total (table : __PREFIX__.Extraction.OrderedCollections.Map)
    (bounded : table.size ≤ 262144)
    (keysValid : table.toList.all (fun pair => decide (pair.1 < 2^64)) = true) :
    ∃ result, __CORE__.entries table = .ok result ∧
      result.val.map (fun row => (row.key.val, row.value)) = table.toList := by
  let snapshot := table.toList.map (fun pair => (__PREFIX__.Extraction.OrderedIterators.keyScalar pair.1, pair.2))
  have sizeBound : snapshot.length ≤ 262144 := by simpa [snapshot] using bounded
  refine ⟨alloc.vec.Vec.from (snapshot.map entry) (by simp; scalar_tac), ?_, ?_⟩
  · apply entries_snapshot table snapshot
    · unfold __PREFIX__.Extraction.OrderedIterators.mapIntoIter
      rw [if_pos ⟨bounded, keysValid⟩]
    · exact sizeBound
  · simp only [alloc.vec.Vec.from_val, snapshot, List.map_map]
    change (table.toList.map (fun pair =>
      ((__PREFIX__.Extraction.OrderedIterators.keyScalar pair.1).val, pair.2))) = table.toList
    conv_rhs => rw [← List.map_id table.toList]
    apply List.map_congr_left
    intro pair present
    have valid : pair.1 < 2^64 := of_decide_eq_true ((List.all_eq_true.mp keysValid) pair present)
    change (pair.1 % 2^64, pair.2) = pair
    rw [Nat.mod_eq_of_lt valid]

theorem members_total (values : __PREFIX__.Extraction.OrderedCollections.Set)
    (bounded : values.size ≤ 262144)
    (keysValid : values.toList.all (fun key => decide (key < 2^64)) = true) :
    ∃ result, __CORE__.members values = .ok result ∧ result.val.map UScalar.val = values.toList := by
  let snapshot := values.toList.map __PREFIX__.Extraction.OrderedIterators.keyScalar
  have sizeBound : snapshot.length ≤ 262144 := by simpa [snapshot] using bounded
  refine ⟨alloc.vec.Vec.from snapshot (by scalar_tac), ?_, ?_⟩
  · apply members_snapshot values snapshot
    · unfold __PREFIX__.Extraction.OrderedIterators.setIntoIter
      rw [if_pos ⟨bounded, keysValid⟩]
    · exact sizeBound
  · simp only [alloc.vec.Vec.from_val, snapshot, List.map_map]
    change (values.toList.map (fun key => (__PREFIX__.Extraction.OrderedIterators.keyScalar key).val)) = values.toList
    conv_rhs => rw [← List.map_id values.toList]
    apply List.map_congr_left
    intro key present
    have valid : key < 2^64 := of_decide_eq_true ((List.all_eq_true.mp keysValid) key present)
    change key % 2^64 = key
    exact Nat.mod_eq_of_lt valid

theorem entries_ordered_unique (table : __PREFIX__.Extraction.OrderedCollections.Map)
    (bounded : table.size ≤ 262144)
    (keysValid : table.toList.all (fun pair => decide (pair.1 < 2^64)) = true) :
    ∃ result, __CORE__.entries table = .ok result ∧
      (result.val.map (fun row => row.key.val)).Pairwise (fun left right => compare left right = .lt) ∧
      (result.val.map (fun row => row.key.val)).Nodup := by
  obtain ⟨result, returned, contents⟩ := entries_total table bounded keysValid
  have keys : result.val.map (fun row => row.key.val) = table.keys := by
    simpa [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) contents
  refine ⟨result, returned, ?_, ?_⟩
  · simpa only [keys] using table.ordered_keys
  · simpa only [keys] using table.nodup_keys

theorem members_ordered_unique (values : __PREFIX__.Extraction.OrderedCollections.Set)
    (bounded : values.size ≤ 262144)
    (keysValid : values.toList.all (fun key => decide (key < 2^64)) = true) :
    ∃ result, __CORE__.members values = .ok result ∧
      (result.val.map UScalar.val).Pairwise (fun left right => compare left right = .lt) ∧
      (result.val.map UScalar.val).Nodup := by
  obtain ⟨result, returned, contents⟩ := members_total values bounded keysValid
  refine ⟨result, returned, ?_, ?_⟩
  · rw [contents]; exact values.ordered_toList
  · rw [contents]; exact values.distinct_toList.imp Std.ReflCmp.ne_of_cmp_ne_eq

private theorem map_single (key : Nat) (value : U64) :
    (({} : __PREFIX__.Extraction.OrderedCollections.Map).insert key value).toList = [(key, value)] := by
  have emptyList : ({} : __PREFIX__.Extraction.OrderedCollections.Map).toList = [] := by rfl
  apply List.perm_singleton.mp
  simpa [emptyList] using (Std.TreeMap.toList_insert_perm (t := ({} : __PREFIX__.Extraction.OrderedCollections.Map)) (k := key) (v := value))

private theorem map_two (first second : Nat) (left right : U64) :
    ((({} : __PREFIX__.Extraction.OrderedCollections.Map).insert first left).insert second right).toList =
      if first = second then [(second, right)]
      else if first < second then [(first, left), (second, right)] else [(second, right), (first, left)] := by
  let table := (({} : __PREFIX__.Extraction.OrderedCollections.Map).insert first left).insert second right
  have perm := Std.TreeMap.toList_insert_perm
    (t := ({} : __PREFIX__.Extraction.OrderedCollections.Map).insert first left) (k := second) (v := right)
  rw [map_single] at perm
  by_cases same : first = second
  · simp only [if_pos same]
    apply List.perm_singleton.mp
    simpa [same] using perm
  · simp only [if_neg same]
    have both : table.toList.Perm [(second, right), (first, left)] := by
      simpa [Ne.symm same] using perm
    have sorted : table.toList.Pairwise (fun a b => a.1 < b.1) := by
      have ordered := table.ordered_keys
      rw [← Std.TreeMap.map_fst_toList_eq_keys] at ordered
      simpa only [List.pairwise_map, Nat.compare_eq_lt] using ordered
    rcases List.perm_pair.mp both with forward | reverse
    · rw [forward] at sorted
      have less : ¬first < second := by simp at sorted; omega
      simpa [less] using forward
    · rw [reverse] at sorted
      have less : first < second := by simpa using sorted
      simpa [less] using reverse

private theorem set_single (key : Nat) :
    (({} : __PREFIX__.Extraction.OrderedCollections.Set).insert key).toList = [key] := by
  have emptyList : ({} : __PREFIX__.Extraction.OrderedCollections.Set).toList = [] := by rfl
  apply List.perm_singleton.mp
  simpa [emptyList] using (Std.TreeSet.toList_insert_perm (t := ({} : __PREFIX__.Extraction.OrderedCollections.Set)) (k := key))

private theorem set_two (first second : Nat) :
    ((({} : __PREFIX__.Extraction.OrderedCollections.Set).insert first).insert second).toList =
      if first = second then [second]
      else if first < second then [first, second] else [second, first] := by
  let values := (({} : __PREFIX__.Extraction.OrderedCollections.Set).insert first).insert second
  have perm := Std.TreeSet.toList_insert_perm
    (t := ({} : __PREFIX__.Extraction.OrderedCollections.Set).insert first) (k := second)
  rw [set_single] at perm
  by_cases same : first = second
  · simp only [if_pos same]
    apply List.perm_singleton.mp
    simpa [same] using perm
  · simp only [if_neg same]
    have both : values.toList.Perm [second, first] := by simpa [same, Ne.symm same] using perm
    rcases List.perm_pair.mp both with forward | reverse
    · have sorted := values.ordered_toList
      rw [forward] at sorted
      have less : ¬first < second := by simp [Nat.compare_eq_lt] at sorted; omega
      simpa [less] using forward
    · have sorted := values.ordered_toList
      rw [reverse] at sorted
      have less : first < second := by simpa [Nat.compare_eq_lt] using sorted
      simpa [less] using reverse

@[expose] def rows (firstKey firstValue secondKey secondValue : U64) : List __CORE__.Entry :=
  if firstKey.val = secondKey.val then [{ key := secondKey, value := secondValue }]
  else if firstKey.val < secondKey.val then
    [{ key := firstKey, value := firstValue }, { key := secondKey, value := secondValue }]
  else [{ key := secondKey, value := secondValue }, { key := firstKey, value := firstValue }]

@[expose] def keys (first second : U64) : List U64 :=
  if first.val = second.val then [second]
  else if first.val < second.val then [first, second] else [second, first]

private theorem map_snapshot_two (firstKey firstValue secondKey secondValue : U64) :
    __PREFIX__.Extraction.OrderedIterators.mapIntoIter
      ((({} : __PREFIX__.Extraction.OrderedCollections.Map).insert firstKey.val firstValue).insert secondKey.val secondValue) =
      .ok ((rows firstKey firstValue secondKey secondValue).map (fun row => (row.key, row.value))) := by
  have one : firstKey.val < 18446744073709551616 := by scalar_tac
  have two : secondKey.val < 18446744073709551616 := by scalar_tac
  by_cases same : firstKey.val = secondKey.val
  · have equal : firstKey = secondKey := by scalar_tac
    subst secondKey
    simp [__PREFIX__.Extraction.OrderedIterators.mapIntoIter, map_two,
      Std.TreeMap.size_insert, one, rows]
  · by_cases less : firstKey.val < secondKey.val <;>
      simp [__PREFIX__.Extraction.OrderedIterators.mapIntoIter, map_two,
        Std.TreeMap.size_insert, same, Ne.symm same, less, one, two, rows]

private theorem set_snapshot_two (first second : U64) :
    __PREFIX__.Extraction.OrderedIterators.setIntoIter
      ((({} : __PREFIX__.Extraction.OrderedCollections.Set).insert first.val).insert second.val) =
      .ok (keys first second) := by
  have one : first.val < 18446744073709551616 := by scalar_tac
  have two : second.val < 18446744073709551616 := by scalar_tac
  by_cases same : first.val = second.val
  · have equal : first = second := by scalar_tac
    subst second
    simp [__PREFIX__.Extraction.OrderedIterators.setIntoIter, set_two,
      Std.TreeSet.size_insert, one, keys]
  · by_cases less : first.val < second.val <;>
      simp [__PREFIX__.Extraction.OrderedIterators.setIntoIter, set_two,
        Std.TreeSet.size_insert, same, Ne.symm same, less, one, two, keys]

private theorem entries_two (firstKey firstValue secondKey secondValue : U64) :
    __CORE__.entries ((({} : __PREFIX__.Extraction.OrderedCollections.Map).insert firstKey.val firstValue).insert secondKey.val secondValue) =
      .ok (alloc.vec.Vec.from (rows firstKey firstValue secondKey secondValue) (by
        unfold rows; split <;> (try split) <;> simp <;> scalar_tac)) := by
  have returned := entries_snapshot _ _ (map_snapshot_two firstKey firstValue secondKey secondValue) (by
    unfold rows; split <;> (try split) <;> simp)
  simpa [entry, rows, List.map_map, Function.comp_def] using returned

private theorem members_two (first second : U64) :
    __CORE__.members ((({} : __PREFIX__.Extraction.OrderedCollections.Set).insert first.val).insert second.val) =
      .ok (alloc.vec.Vec.from (keys first second) (by
        unfold keys; split <;> (try split) <;> simp <;> scalar_tac)) := by
  apply members_snapshot _ _ (set_snapshot_two first second)
  unfold keys; split <;> (try split) <;> simp

@[cbv_eval] theorem preview_entries (firstKey firstValue secondKey secondValue : U64) :
    __ANALYSIS__.ordered_entries firstKey firstValue secondKey secondValue =
      .ok (if firstKey.val = secondKey.val then (some secondKey, some secondValue, none, none, 1#u64)
        else if firstKey.val < secondKey.val then
          (some firstKey, some firstValue, some secondKey, some secondValue, 2#u64)
        else (some secondKey, some secondValue, some firstKey, some firstValue, 2#u64)) := by
  by_cases same : firstKey.val = secondKey.val
  · have equal : firstKey = secondKey := by scalar_tac
    subst secondKey
    simp [__ANALYSIS__.ordered_entries, __CORE__.replace_value,
      __PREFIX__.Extraction.OrderedCollections.mapNew, __PREFIX__.Extraction.OrderedCollections.mapInsert, Std.TreeMap.size_insert,
      entries_two, rows, __PREFIX__.Extraction.SliceModel.first,
      __RUST__.core.option.OptionShared0T.copied, alloc.vec.Vec.deref, alloc.vec.Vec.len,
      core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get, lift]
    scalar_tac
  · by_cases less : firstKey.val < secondKey.val <;>
      simp [__ANALYSIS__.ordered_entries, __CORE__.replace_value,
        __PREFIX__.Extraction.OrderedCollections.mapNew, __PREFIX__.Extraction.OrderedCollections.mapInsert, Std.TreeMap.size_insert,
        entries_two, rows, same, Ne.symm same, less, __PREFIX__.Extraction.SliceModel.first,
        __RUST__.core.option.OptionShared0T.copied, alloc.vec.Vec.deref, alloc.vec.Vec.len,
        core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get, lift] <;>
      scalar_tac

@[cbv_eval] theorem preview_members (first second : U64) :
    __ANALYSIS__.ordered_members first second =
      .ok (if first.val = second.val then (some second, none, 1#u64)
        else if first.val < second.val then (some first, some second, 2#u64)
        else (some second, some first, 2#u64)) := by
  by_cases same : first.val = second.val
  · have equal : first = second := by scalar_tac
    subst second
    simp [__ANALYSIS__.ordered_members, __CORE__.claim,
      __PREFIX__.Extraction.OrderedCollections.setNew, __PREFIX__.Extraction.OrderedCollections.setInsert, Std.TreeSet.size_insert,
      members_two, keys, __PREFIX__.Extraction.SliceModel.first,
      __RUST__.core.option.OptionShared0T.copied, alloc.vec.Vec.deref, alloc.vec.Vec.len,
      core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get, lift]
    scalar_tac
  · by_cases less : first.val < second.val <;>
      simp [__ANALYSIS__.ordered_members, __CORE__.claim,
        __PREFIX__.Extraction.OrderedCollections.setNew, __PREFIX__.Extraction.OrderedCollections.setInsert, Std.TreeSet.size_insert,
        members_two, keys, same, Ne.symm same, less, __PREFIX__.Extraction.SliceModel.first,
        __RUST__.core.option.OptionShared0T.copied, alloc.vec.Vec.deref, alloc.vec.Vec.len,
        core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get, lift] <;>
      scalar_tac
end __PREFIX__.Properties
