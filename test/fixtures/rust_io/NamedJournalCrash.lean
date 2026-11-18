module
public import Record.NativeRuntime
public section
open Lynx
namespace Record.NamedJournalCrash
open NativeFile

@[expose] def namedJournal (journalName : ByteArray) : Names := [(journalName, 1)]

@[expose] def inodeIds (env : Environment) : List Nat :=
  (env.nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName)).map Prod.fst

private theorem selected_unique (chosen selected : Names)
    (table : namespaceTable (encodeNames chosen) = some selected) :
    (selected.map (fun entry => entry.1.data)).eraseDups.length = selected.length := by
  simp only [encodeNames, namespaceTable] at table
  split at table
  · contradiction
  · simp only [Bind.bind, Option.bind_eq_some_iff] at table
    rcases table with ⟨mapped, parsed, table⟩
    split at table
    · contradiction
    · rename_i unique
      cases table
      simpa using unique

private theorem selected_is_journal (journalName : ByteArray) (selected : Names) (script : Term)
    (unique : (selected.map (fun entry => entry.1.data)).eraseDups.length = selected.length)
    (allowed : namespaceCrashAllowed ⟨namedJournal journalName, namedJournal journalName, [], script⟩ selected = true) :
    selected = namedJournal journalName := by
  simp [namespaceCrashAllowed, namedJournal, namedInode] at allowed
  have mapped : selected.map (fun entry => entry.1.data) =
      List.replicate selected.length journalName.data := by
    apply List.map_eq_replicate_iff.mpr
    intro entry member
    exact (allowed.1 entry.1 entry.2 member).symm
  rw [mapped] at unique
  rcases allowed.2 with ⟨actual, found⟩
  cases selected with
  | nil => simp at found
  | cons head tail =>
    have empty : tail = [] := by
      have length : tail.length = 0 := by
        simpa [List.replicate_succ, List.eraseDups_cons] using unique.symm
      exact List.eq_nil_of_length_eq_zero length
    subst tail
    have same : head.1 = journalName :=
      ByteArray.ext (allowed.1 head.1 head.2 (by simp)).symm
    obtain ⟨path, node⟩ := head
    simp only at same
    subst path
    simp at found
    simp [namedJournal, found]

private theorem one_inode {α : Type} (items : List α) (tag : α → Nat)
    (ids : items.map tag = [1]) : ∃ node, items = [node] ∧ tag node = 1 := by
  cases items with
  | nil => simp at ids
  | cons node rest =>
    simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at ids
    exact ⟨node, by simp [ids.2], ids.1⟩

theorem captured_journal (journalName : ByteArray) (env : Environment) (disk : State) (script : Term)
    (tables : namespaceSnapshot env = some ⟨namedJournal journalName, namedJournal journalName, [], script⟩)
    (ids : inodeIds env = [1]) (found : inode 1 env = some disk)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks env = some image) :
    ∃ mask bytes, persist disk.durable disk.visible mask = some bytes ∧
      image = ⟨namedJournal journalName, [(1, bytes)], env.nativeRefCounter⟩ := by
  unfold inodeIds at ids
  obtain ⟨node, nodes, nodeId⟩ := one_inode _ _ ids
  unfold filesystemCrashImage at crash
  rw [tables] at crash
  simp only [Bind.bind, Option.bind_some, Option.bind_eq_some_iff] at crash
  obtain ⟨selected, normalized, crash⟩ := crash
  split at crash
  · contradiction
  · rename_i allowed
    have permit : namespaceCrashAllowed ⟨namedJournal journalName, namedJournal journalName, [], script⟩ selected = true := by
      simpa using allowed
    have selectedNames := selected_is_journal journalName selected script
      (selected_unique chosen selected normalized) permit
    rw [nodes] at crash
    split at crash
    · contradiction
    · rename_i aligned
      have maskIds : masks.map Prod.fst = [1] := by
        simpa [nodeId] using aligned
      obtain ⟨⟨number, mask⟩, rfl, entryId⟩ := one_inode masks Prod.fst maskIds
      change number = 1 at entryId
      subst number
      rw [selectedNames] at crash
      change node.1 = 1 at nodeId
      simp [List.mapM, List.mapM.loop, nodeId, found] at crash
      cases choice : persist disk.durable disk.visible mask with
      | none => simp [choice] at crash
      | some bytes =>
        simp [choice, namedJournal] at crash
        exact ⟨mask, bytes, by simp [choice], crash.symm⟩

theorem names_equal (left right : NativeFile.Names)
    (equal : NativeFile.tablesEqual left right = true) : left = right := by
  have mapped : left.map (fun entry => (entry.1.data,entry.2)) =
      right.map (fun entry => (entry.1.data,entry.2)) := by
    simpa only [NativeFile.tablesEqual,beq_iff_eq] using equal
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons first rest ih =>
    cases right with
    | nil => simp at mapped
    | cons second tail =>
      simp only [List.map_cons,List.cons.injEq] at mapped
      have head : first = second := by
        obtain ⟨⟨a⟩,i⟩ := first
        obtain ⟨⟨b⟩,j⟩ := second
        simp only [Prod.mk.injEq] at mapped
        obtain ⟨⟨rfl,rfl⟩,tail⟩ := mapped
        rfl
      apply congrArg₂ List.cons head
      apply ih tail
      all_goals simpa only [NativeFile.tablesEqual,beq_iff_eq] using mapped.2

private theorem persist_lengths (old visible mask result : ByteArray)
    (accepted : persist old visible mask = some result) :
    min old.size visible.size ≤ result.size ∧ result.size ≤ max old.size visible.size := by
  unfold persist at accepted
  split at accepted
  · rename_i conditions
    cases accepted
    simpa [← ByteArray.size_data] using And.intro conditions.1 conditions.2.1
  · contradiction

private theorem persist_at (old visible mask result : ByteArray)
    (accepted : persist old visible mask = some result) (i : Nat) (inside : i < result.size) :
    result[i]! = if mask[i]! == 1 then visible[i]! else old[i]! := by
  unfold persist at accepted
  split at accepted
  · cases accepted
    have inbound : i < mask.size := by simpa [← ByteArray.size_data] using inside
    rw [getElem!_pos (⟨mask.data.mapIdx fun index choice =>
      if choice == 1 then visible[index]! else old[index]!⟩ : ByteArray) i inside,
      getElem!_pos mask i inbound]
    change (mask.data.mapIdx _)[i] = _
    simp only [_root_.Array.getElem_mapIdx]
    rfl
  · contradiction

/-- Bytes may contain a short partial record after the complete known prefix. -/
@[expose] def JournalBytes (head data : ByteArray) : Prop :=
  (head.size ≤ data.size ∧ ∀ i, i < head.size → data[i]! = head[i]!) ∧
    data.size < head.size + 4

/-- Every bytewise crash choice extends the same known prefix by less than one
record when both the visible and durable file images have that shape. -/
theorem persist_journal (head old visible mask result : ByteArray)
    (oldImage : JournalBytes head old) (visibleImage : JournalBytes head visible)
    (accepted : persist old visible mask = some result) : JournalBytes head result := by
  have sizes := persist_lengths old visible mask result accepted
  refine ⟨⟨by have := oldImage.1.1; have := visibleImage.1.1; omega, ?_⟩,
    by have := oldImage.2; have := visibleImage.2; omega⟩
  intro i inside
  rw [persist_at old visible mask result accepted i (by
    have := oldImage.1.1; have := visibleImage.1.1; omega)]
  split
  · exact visibleImage.1.2 i inside
  · exact oldImage.1.2 i inside

end Record.NamedJournalCrash
