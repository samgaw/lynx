module
public import Record.NamedConcurrentRepairWriter
public import Record.ConcurrentRepairWriterRecovery

public section
open Aeneas Aeneas.Std Lynx io_protocol NativeFile

namespace Record.NamedConcurrentWriterCrash
open Record.NamedConcurrentRepairWriter
open Record.ConcurrentRepairWriterInvariant (snapshot admittedBytes ordered reversed
  firstProtected secondProtected bothProtected)
open Record.NamedJournalCrash (namedJournal captured_journal inodeIds)
open Record.CrashProperties (disk)
open Record.LogProperties (logBytes)
open Record.ConcurrentRepairWriterRecovery (base_image common_records)
open Record.EncodedPrefixRecovery (persist_prefix)
open Record.RepairCrashProperties (Prefix persist_lengths)

private theorem names_eq (actual expected : Names) (equal : tablesEqual actual expected = true) :
    actual = expected := by
  unfold tablesEqual at equal
  have same := beq_iff_eq.mp equal
  clear equal
  induction actual generalizing expected with
  | nil => cases expected <;> simp_all
  | cons first rest ih =>
    cases expected with
    | nil => simp at same
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at same
      obtain ⟨⟨path, id⟩, next⟩ := same
      have head : first = other := Prod.ext (ByteArray.ext path) id
      rw [head, ih tail next]

private theorem bytes_eq (a b : ByteArray) (equal : (a == b) = true) : a = b := by
  change (a.data == b.data) = true at equal
  exact ByteArray.ext (beq_iff_eq.mp equal)

private theorem exact_table (table : NamespaceSnapshot)
    (live : tablesEqual table.names names = true) (durable : tablesEqual table.committed names = true)
    (pending : table.pending.isEmpty = true) (script : (table.script == Term.nil) = true) :
    table = ⟨names, names, [], .nil⟩ := by
  cases table with
  | mk a b c d =>
    have eqA := names_eq _ _ live
    have eqB := names_eq _ _ durable
    have eqC := List.isEmpty_iff.mp pending
    have eqD : d = .nil :=
      (Term.compare_eq_nil _).mp ((Term.beq_iff_compare_eq _ _).mp script)
    cases eqA; cases eqB; cases eqC; cases eqD
    rfl

set_option maxRecDepth 8192 in
/-- A completed contending execution reports both appends in one serial order.
Every admitted power loss of that actual named-inode state captures the same bytes. -/
theorem terminal_crash (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term) (outcome : Outcome Term)
    (run : Concurrent.Run (.start initial (writers locked_repair_and_append) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (snapshot last) = some image) :
    outcome = .ok Term.true ∧
    ∃ values : List U16, (values = [13#u16,19#u16,23#u16] ∨ values = [13#u16,23#u16,19#u16]) ∧
      image = ⟨names, [(1, disk (logBytes values))], (snapshot last).nativeRefCounter⟩ := by
  have checked := Concurrent.checkInvariant_sound (named_prefixes_checked elapsed) run
  unfold safe at checked
  dsimp only at checked
  split at checked
  · rename_i node table found tables
    simp only [terminal.successors_eq_nil, List.isEmpty_nil, Bool.not_true, Bool.false_or,
      Bool.and_eq_true] at checked
    obtain ⟨kept, completed⟩ := checked
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨live, durable⟩, pending⟩, script⟩, ids⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := kept
    obtain ⟨⟨⟨⟨reported, _⟩, _⟩, serial⟩, _⟩ := completed
    have actual : last.outcome = .ok Term.true := by
      split at reported
      · rename_i value returned
        have eq : value = Term.true :=
          (Term.compare_eq_atom _ _).mp ((Term.beq_iff_compare_eq _ _).mp reported)
        exact returned.trans (congrArg Outcome.ok eq)
      · contradiction
    obtain ⟨mask, bytes, persisted, captured⟩ := captured_journal journal (snapshot last) node .nil
      (tables.trans (congrArg some (exact_table table live durable pending script))) (beq_iff_eq.mp ids) found chosen masks image crash
    refine ⟨terminal.outcome_eq.symm.trans actual, ?_⟩
    simp only [bothProtected, Bool.or_eq_true, Bool.and_eq_true] at serial
    rcases serial with h | h
    · rw [bytes_eq _ _ h.1, bytes_eq _ _ h.2] at persisted
      exact ⟨[13#u16,19#u16,23#u16], .inl rfl, by rw [captured, NativeFile.persist_same _ _ _ persisted]; rfl⟩
    · rw [bytes_eq _ _ h.1, bytes_eq _ _ h.2] at persisted
      exact ⟨[13#u16,23#u16,19#u16], .inr rfl, by rw [captured, NativeFile.persist_same _ _ _ persisted]; rfl⟩
  · contradiction

set_option maxRecDepth 8192 in
/-- Every admitted crash at a reachable prefix of the two-writer run retains
all observed acknowledgements in a complete prefix of the named inode. -/
theorem prefix_crash (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term)
    (run : Concurrent.Run (.start initial (writers locked_repair_and_append) elapsed) events last)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (snapshot last) = some image) :
    ∃ (values : List U16) (bytes : ByteArray),
      image = ⟨names, [(1, bytes)], (snapshot last).nativeRefCounter⟩ ∧
      1 ≤ image.highWater ∧ bytes.size ≤ limit ∧ values.length ≤ 262144 ∧
      Prefix (disk (logBytes values)) bytes ∧ 13#u16 ∈ values ∧
      (acknowledged 19 (snapshot last) = true → 19#u16 ∈ values) ∧
      (acknowledged 23 (snapshot last) = true → 23#u16 ∈ values) := by
  have checked := Concurrent.checkInvariant_sound (named_prefixes_checked elapsed) run
  unfold safe at checked
  dsimp only at checked
  split at checked
  · rename_i node table found tables
    simp only [Bool.and_eq_true] at checked
    obtain ⟨kept, _⟩ := checked
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨live, durable⟩, pending⟩, script⟩, ids⟩, counter⟩, v⟩, d⟩, first⟩, second⟩, both⟩ := kept
    have clockBound : 1 ≤ (snapshot last).nativeRefCounter := of_decide_eq_true counter
    obtain ⟨mask, bytes, persisted, captured⟩ := captured_journal journal (snapshot last) node .nil
      (tables.trans (congrArg some (exact_table table live durable pending script)))
      (beq_iff_eq.mp ids) found chosen masks image crash
    obtain ⟨values, capacity, oldRecord, firstRecord, secondRecord, visiblePrefix, durablePrefix⟩ :=
      common_records (acknowledged 19 (snapshot last)) (acknowledged 23 (snapshot last))
        node v d first second both
    have sizes := persist_lengths _ _ _ _ persisted
    have vb := (base_image _ v).2
    have db := (base_image _ d).2
    refine ⟨values, bytes, captured, ?_, by omega, capacity,
      persist_prefix _ _ _ _ _ durablePrefix visiblePrefix persisted, oldRecord, firstRecord, secondRecord⟩
    rw [captured]
    exact clockBound
  · contradiction

end Record.NamedConcurrentWriterCrash
