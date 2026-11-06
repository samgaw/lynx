module
public import Runtime.Mutex.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.MutexProperties

/-- The extracted cross-crate callee computes the sum or preserves the counter. -/
theorem increment_spec (counter : effects_core.Counter) (amount : U64) :
    ∃ success updated, effects_core.increment counter amount = Result.ok (success, updated) ∧
      (if success then updated.value.val = counter.value.val + amount.val
       else updated = counter ∧ U64.max < counter.value.val + amount.val) := by
  have arithmetic := U64.checked_add_bv_spec counter.value amount
  cases checked : U64.checked_add counter.value amount with
  | none =>
    refine ⟨false, counter, ?_, ?_⟩
    · simp [effects_core.increment, NativeM.lift, NativeM.ok, checked]
    · simpa [checked] using arithmetic
  | some value =>
    refine ⟨true, ⟨value⟩, ?_, ?_⟩
    · simp [effects_core.increment, NativeM.lift, NativeM.ok, checked]
    · have found := arithmetic
      simp only [checked] at found
      exact found.2.1

/-- The actual factory stores the result of the verified first-party update in
one fresh unlocked, unpoisoned shared cell, preserving all existing cells. -/
theorem initialized (value amount : U64) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    ∃ (changed : Bool) (counter : effects_core.Counter),
      (if changed then counter.value.val = value.val + amount.val
       else counter.value = value ∧ U64.max < value.val + amount.val) ∧
      mutex_new_incremented value amount env =
        (.ok (changed, ⟨env.refCounter + 1⟩),
          { env with
            refCounter := env.refCounter + 1
            nativeHeap := (env.refCounter + 1, NativeMutex.typeName effects_core.Counter,
              .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode counter]) :: env.nativeHeap }) ∧
      NativeCodec.decode (NativeCodec.encode counter) = some counter := by
  obtain ⟨changed, counter, returned, property⟩ := increment_spec ⟨value⟩ amount
  refine ⟨changed, counter, ?_, ?_, NativeCodec.roundtrip _⟩
  · cases changed <;> simp_all
  · simp [mutex_new_incremented, returned, NativeM.ok, NativeMutex.new, NativeM.allocate, fresh]

/-- Observe the freshly returned owning handle before any destruction. This is
an observation of the modelled heap, not a Rust lock acquisition or drop. -/
theorem initialized_readback (value amount : U64) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    ∃ (changed : Bool) (counter : effects_core.Counter),
      let stored := Term.tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode counter]
      let after : Environment := { env with
        refCounter := env.refCounter + 1
        nativeHeap := (env.refCounter + 1, NativeMutex.typeName effects_core.Counter, stored) :: env.nativeHeap }
      mutex_new_incremented value amount env = (.ok (changed, ⟨env.refCounter + 1⟩), after) ∧
      NativeM.readCell (NativeMutex.typeName effects_core.Counter) (env.refCounter + 1) after =
        (.ok stored, after) ∧ NativeCodec.decode (NativeCodec.encode counter) = some counter := by
  obtain ⟨changed, counter, _, returned, roundtrip⟩ := initialized value amount env fresh
  refine ⟨changed, counter, returned, ?_, roundtrip⟩
  have absent : env.nativeHeap.filter (fun cell => cell.1 == env.refCounter + 1) = [] := by
    simpa only [List.filter_eq_nil_iff, List.any_eq_false] using fresh
  simp [NativeM.readCell, absent]

/-- An inconsistent identity supply cannot overwrite a live native cell. -/
theorem collision_exhausts (value amount : U64) (env : Environment)
    (collision : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = true) :
    mutex_new_incremented value amount env = (.error .exhausted, env) := by
  obtain ⟨changed, counter, returned, _⟩ := increment_spec ⟨value⟩ amount
  simp [mutex_new_incremented, returned, NativeM.ok, NativeMutex.new, NativeM.allocate, collision]

/-- Automatically derived codecs compose over actual nested workspace structs. -/
theorem snapshot_initialized (value : U64) (enabled : Bool) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    let snapshot : effects_core.Snapshot := { enabled, counter := { value } }
    mutex_snapshot value enabled env =
      (.ok ⟨env.refCounter + 1⟩, { env with
        refCounter := env.refCounter + 1
        nativeHeap := (env.refCounter + 1, NativeMutex.typeName effects_core.Snapshot,
          .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode snapshot]) :: env.nativeHeap }) ∧
      NativeCodec.decode (NativeCodec.encode snapshot) = some snapshot := by
  constructor
  · simp [mutex_snapshot, NativeMutex.new, NativeM.allocate, fresh]
  · exact NativeCodec.roundtrip _

/-- Sequential constructors preserve both cells and return distinct owning identities. -/
theorem paired_identities (first second : U64) (env : Environment)
    (freshFirst : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false)
    (freshSecond : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 2) = false) :
    mutex_pair first second env =
      (.ok (⟨env.refCounter + 1⟩, ⟨env.refCounter + 2⟩), { env with
        refCounter := env.refCounter + 2
        nativeHeap :=
          (env.refCounter + 2, NativeMutex.typeName effects_core.Counter,
            .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (effects_core.Counter.mk second)]) ::
          (env.refCounter + 1, NativeMutex.typeName effects_core.Counter,
            .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (effects_core.Counter.mk first)]) ::
          env.nativeHeap }) ∧ env.refCounter + 1 ≠ env.refCounter + 2 := by
  simp [mutex_pair, NativeMutex.new, NativeM.allocate, NativeM.ok,
    freshFirst, freshSecond, Nat.add_assoc]

end Runtime.MutexProperties
