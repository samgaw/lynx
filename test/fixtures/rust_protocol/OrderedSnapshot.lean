module
public import __PREFIX__.Properties
public section
open Aeneas Aeneas.Std Lynx
open __PREFIX__.Extraction.OrderedCollections __PREFIX__.Extraction.OrderedIterators
unseal RustM
namespace __PREFIX__.Snapshots

theorem pairs_fuel (remaining : MapIterator) (output : alloc.vec.Vec (U64 × U64))
    (fuel : Nat) (enough : remaining.length < fuel)
    (bounded : output.val.length + remaining.length ≤ 262144) :
    ∃ result, NativeM.loopFuel (fun state => __CORE__.pairs_loop.body state.1 state.2)
        fuel (remaining, output) = NativeM.ok result ∧
      result.val = output.val ++ remaining := by
  induction remaining generalizing output fuel with
  | nil =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      refine ⟨output, ?_, by simp⟩
      simp [NativeM.loopFuel, __CORE__.pairs_loop.body, mapNext, NativeM.ok]
  | cons pair tail ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have room : output.val.length + 1 ≤ U32.max := by simp at bounded; scalar_tac
      have grow : output.val.length < 262144 := by simp at bounded; omega
      let next := alloc.vec.Vec.from (output.val ++ [pair]) (by simp; scalar_tac)
      have pushed : __PREFIX__.Extraction.VectorModel.push output pair = RustM.ok next := by
        rw [__PREFIX__.Extraction.VectorModel.push_within output pair grow]
        simp [alloc.vec.Vec.push, room, next]
      have nextBound : next.val.length + tail.length ≤ 262144 := by
        simp [next]; simp at bounded; omega
      have nextFuel : tail.length < fuel := by simp at enough; omega
      obtain ⟨result, returned, values⟩ := ih next fuel nextFuel nextBound
      refine ⟨result, ?_, by simpa [next, List.append_assoc] using values⟩
      have remainingBound : tail.length < 262144 := by simp at bounded; omega
      simpa [NativeM.loopFuel, __CORE__.pairs_loop.body, mapNext, remainingBound,
        pushed, NativeM.ok] using returned

theorem pairs_snapshot (table : Map) (snapshot : MapIterator)
    (decoded : mapIntoIter table = RustM.ok snapshot) (bounded : snapshot.length ≤ 262144) :
    __CORE__.pairs table = NativeM.ok (alloc.vec.Vec.from snapshot (by scalar_tac)) := by
  obtain ⟨result, returned, values⟩ := pairs_fuel snapshot (alloc.vec.Vec.new (U64 × U64))
    262145 (by omega) (by simpa [alloc.vec.Vec.new] using bounded)
  have same : result = alloc.vec.Vec.from snapshot (by scalar_tac) := by
    apply alloc.vec.Vec.ext
    simpa [alloc.vec.Vec.new] using values
  simp [__CORE__.pairs, __CORE__.pairs_loop, NativeM.loop, decoded, returned, same]

theorem pairs_outcome (table : Map) :
    __CORE__.pairs table =
      if admitted : table.size ≤ 262144 ∧
          table.toList.all (fun row => decide (row.1 < 2^64)) = true then
        NativeM.ok (alloc.vec.Vec.from
          (table.toList.map (fun row => (keyScalar row.1, row.2)))
          (by simp; have := admitted.1; scalar_tac))
      else Result.error .exhausted := by
  by_cases admitted : table.size ≤ 262144 ∧
      table.toList.all (fun row => decide (row.1 < 2^64)) = true
  · rw [dite_eq_left admitted]
    apply pairs_snapshot table
    · unfold mapIntoIter
      exact ite_eq_left admitted
    · simpa using admitted.1
  · rw [dite_eq_right admitted]
    have exhausted : mapIntoIter table = RustM.fail .undef := by
      unfold mapIntoIter
      exact ite_eq_right admitted
    simp [__CORE__.pairs, exhausted]

theorem pairs_total (table : Map) (bounded : table.size ≤ 262144)
    (valid : table.toList.all (fun row => decide (row.1 < 2^64)) = true) :
    ∃ result, __CORE__.pairs table = NativeM.ok result ∧
      result.val.map (fun row => (row.1.val, row.2)) = table.toList := by
  let snapshot := table.toList.map (fun row => (keyScalar row.1, row.2))
  have length : snapshot.length ≤ 262144 := by simpa [snapshot] using bounded
  refine ⟨alloc.vec.Vec.from snapshot (by scalar_tac), ?_, ?_⟩
  · apply pairs_snapshot table snapshot
    · unfold mapIntoIter
      exact if_pos ⟨bounded, valid⟩
    · exact length
  · simp only [alloc.vec.Vec.from_val, snapshot, List.map_map]
    conv_rhs => rw [← List.map_id table.toList]
    apply List.map_congr_left
    intro row present
    have keyBound : row.1 < 2^64 := of_decide_eq_true ((List.all_eq_true.mp valid) row present)
    change (row.1 % 2^64, row.2) = row
    rw [Nat.mod_eq_of_lt keyBound]


theorem pairs_contract (table : NativeMutex Map) :
    __CORE__.locked_pairs table = (do
      let acquired ← NativeMutex.lock table
      let guard := match acquired with | .Ok guard => guard | .Err error => error.value
      let snapshot ← __CORE__.pairs guard.value
      NativeGuard.release guard
      .ok snapshot) := by
  simp [__CORE__.locked_pairs, NativeGuard.deref, NativeDrop.drop, NativeOwnedDrop.drop,
    NativeM.lift, NativeM.ok]
  congr 1
  funext acquired
  cases acquired <;> simp [NativePoisonError.into_inner]

theorem pairs_run (table : Map) (poisoned : Bool) (bounded : table.size ≤ 262144)
    (valid : table.toList.all (fun row => decide (row.1 < 2^64)) = true)
    (env : Environment) (schedule : List ScheduleChoice) :
    (__ANALYSIS__.registry_pairs ⟨1⟩).run (__PREFIX__.Properties.state table poisoned env) schedule =
      (.ok (alloc.vec.Vec.from (table.toList.map (fun row => (keyScalar row.1, row.2)))
        (by simp; scalar_tac)),
        {__PREFIX__.Properties.state table poisoned env with nativeRefCounter := 2}) := by
  have observed := pairs_snapshot table
    (table.toList.map (fun row => (keyScalar row.1, row.2)))
    (by unfold mapIntoIter; exact if_pos ⟨bounded, valid⟩) (by simpa using bounded)
  cases poisoned <;>
    simp [__ANALYSIS__.registry_pairs, pairs_contract, __PREFIX__.Properties.state, NativeMutex.lock,
      NativeMutex.pollLock, NativeCodec.roundtrip, observed, NativeGuard.release,
      NativeGuard.pollRelease, NativeM.ok, Result.wait_run, Result.wait_bind]

theorem fuel_zero (remaining : MapIterator) (output : alloc.vec.Vec (U64 × U64)) :
    NativeM.loopFuel (fun state => __CORE__.pairs_loop.body state.1 state.2)
      0 (remaining, output) = Result.error .exhausted := rfl

end __PREFIX__.Snapshots
