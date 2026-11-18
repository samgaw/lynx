module
public import Record.NamedRepairCrash

public section

open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol

namespace Record.NamedCloseInvariant
open NativeFile
open Record.FileView (namedWorld NamedSeparated handleCell inodeCell named_load named_store)
open Record.ResizeProperties (Admitted)
open Record.RepairCrashProperties (LogImage persist_lengths persist_log_image)

private def closedWorld (number : Nat) (env : Environment) (file : NativeFile) (state : State)
    (frame : List (Nat × String × Term)) : Environment :=
  { namedWorld number env file state frame with nativeHeap :=
    (file.id, closedHandleTypeName, encodeHandle ⟨number, state.position, state.script⟩) ::
      frame ++ [inodeCell number state] }

private theorem retire_named (number : Nat) (env : Environment) (file : NativeFile)
    (before after : State) (frame : List (Nat × String × Term))
    (separate : NamedSeparated number file frame) (valid : Admitted before) :
    retire file after (namedWorld number env file before frame) =
      closedWorld number env file after frame := by
  obtain ⟨fileNonzero, nodeNonzero, different, fileFrame, nodeFrame⟩ := separate
  have absent : frame.filter (fun cell => cell.1 == file.id) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro cell member
    simpa using fileFrame cell member
  have found : (namedWorld number env file before frame).nativeHeap.filter
      (fun cell => cell.1 == file.id) = [handleCell number file before] := by
    simp [namedWorld, handleCell, inodeCell, List.filter_append, absent, different, Ne.symm different]
  have decoded : decodeHandle (encodeHandle ⟨number, before.position, before.script⟩) =
      some ⟨number, before.position, before.script⟩ := by
    simp [decodeHandle, encodeHandle, nodeNonzero, not_lt.mpr valid.2.2,
      not_lt.mpr (Int.natCast_nonneg before.position)]
  have changes : sharedStore file ⟨number, before.position, before.script⟩ after
      (namedWorld number env file before frame) = namedWorld number env file after frame := by
    simpa [store, found, handleCell, typeName, handleTypeName, writableHandleTypeName, decoded] using
      named_store number env file before after frame ⟨fileNonzero, nodeNonzero, different, fileFrame, nodeFrame⟩ valid
  have fixed : frame.map (fun cell =>
      if cell.1 = file.id then (file.id, closedHandleTypeName, cell.2.2) else cell) = frame := by
    conv_rhs => rw [← List.map_id frame]
    exact List.map_congr_left (fun cell member => by simp [fileFrame cell member])
  simp only [retire, found, handleCell, typeName, handleTypeName, writableHandleTypeName, decoded,
    Bool.false_eq_true, ↓reduceIte, Bool.false_or, Bool.or_true, changes]
  simp [closedWorld, namedWorld, handleCell, inodeCell, List.map_append, fixed, Ne.symm different]

private theorem closed_handle_rejected (number : Nat) (env : Environment) (file : NativeFile)
    (state : State) (frame : List (Nat × String × Term))
    (separate : NamedSeparated number file frame) :
    lookup file (closedWorld number env file state frame) = none ∧
    pollClose file (closedWorld number env file state frame) =
      some (.error .exhausted, closedWorld number env file state frame) := by
  obtain ⟨nonzero, _, different, fileFrame, _⟩ := separate
  have absent : frame.filter (fun cell => cell.1 == file.id) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro cell member
    simpa using fileFrame cell member
  have fileBound : file.id ≤ max env.nativeRefCounter (max file.id number) := by omega
  have missing : lookup file (closedWorld number env file state frame) = none := by
    simp [lookup, sharedLookup, getHandle, closedWorld, namedWorld, inodeCell,
      List.filter_append, absent, different, Ne.symm different, nonzero, not_lt.mpr fileBound,
      typeName, handleTypeName, writableHandleTypeName, closedHandleTypeName]
  refine ⟨missing, ?_⟩
  simp only [pollClose, missing]
  simp [pollDirectoryClose, directoryHandle, closedWorld, namedWorld, inodeCell, encodeHandle,
    List.filter_append, absent, different, Ne.symm different, nonzero, not_lt.mpr fileBound,
    directoryTypeName, closedHandleTypeName]

private theorem close_return_retires (number : Nat) (env : Environment) (file : NativeFile)
    (before : State) (frame : List (Nat × String × Term)) (after : Environment)
    (separate : NamedSeparated number file frame) (valid : Admitted before)
    (closed : Result.ReadyPrefix (NativeOwnedDrop.drop file) (namedWorld number env file before frame)
      (.ok ()) after) :
    lookup file after = none ∧ pollClose file after = some (.error .exhausted, after) := by
  simp only [NativeOwnedDrop.drop, NativeFile.close] at closed
  obtain ⟨reply, middle, ready, tail⟩ := closed.wait_returns
  cases reply with
  | error exception => cases tail
  | ok unit =>
    obtain ⟨rfl, rfl⟩ := tail.ok_returns
    simp only [pollClose, named_load number env file before frame separate valid] at ready
    by_cases stopped : blocked before = true
    · simp [stopped] at ready
    · simp only [stopped] at ready
      cases stepped : closeStep before with
      | none => simp [stepped] at ready
      | some state =>
        simp only [stepped, Option.some.injEq, Prod.mk.injEq,
          retire_named number env file before state frame separate valid] at ready
        obtain ⟨_, rfl⟩ := ready
        exact closed_handle_rejected number env file state frame separate

/-- An admitted close consumes the descriptor and preserves the acknowledged
log even if the host close fails or changes which suffix bytes persist. -/
private theorem close_step_preserves (values : List U16) (before after : State)
    (valid : Admitted before) (visible : LogImage values before.visible) (durable : LogImage values before.durable)
    (stepped : closeStep before = some after) :
    Admitted after ∧ LogImage values after.visible ∧ LogImage values after.durable := by
  simp only [closeStep, Option.bind_eq_bind] at stepped
  generalize action "close" before.script = choice at stepped
  cases choice with
  | none => contradiction
  | some choice =>
    obtain ⟨success, value, mask, rest⟩ := choice
    simp only [Option.bind_some] at stepped
    split at stepped
    · contradiction
    · cases saved : persist before.durable before.visible mask with
      | none => simp [saved] at stepped
      | some result =>
        simp only [saved, Option.bind_some, Option.some.injEq] at stepped
        subst after
        have lengths := persist_lengths _ _ _ _ saved
        have first := valid.1
        have second := valid.2.1
        exact ⟨⟨first, by dsimp; omega, valid.2.2⟩, visible,
          persist_log_image values _ _ _ _ durable visible saved⟩

private def JournalState (number : Nat) (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (world : Environment) : Prop :=
  ∃ state, (world = namedWorld number env file state frame ∨ world = closedWorld number env file state frame) ∧
    Admitted state ∧ LogImage values state.visible ∧ LogImage values state.durable

private theorem close_invariant (number : Nat) (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16)
    (separate : NamedSeparated number file frame) (valid : Admitted before)
    (visible : LogImage values before.visible) (durable : LogImage values before.durable) :
    Result.NativeInvariant (JournalState number env file frame values) (NativeOwnedDrop.drop file)
      (namedWorld number env file before frame) := by
  have initial : JournalState number env file frame values (namedWorld number env file before frame) :=
    ⟨before, .inl rfl, valid, visible, durable⟩
  simp only [NativeOwnedDrop.drop, NativeFile.close]
  apply Result.NativeInvariant.wait _ _ _ initial
  intro reply world ready
  simp only [pollClose, named_load number env file before frame separate valid] at ready
  by_cases stopped : blocked before = true
  · simp [stopped] at ready
  · simp only [stopped] at ready
    cases stepped : closeStep before with
    | none =>
      simp only [stepped, Option.some.injEq, Prod.mk.injEq] at ready
      obtain ⟨rfl, rfl⟩ := ready
      exact .error _ _ _ initial
    | some after =>
      simp only [stepped, Option.some.injEq, Prod.mk.injEq, retire_named number env file before after frame separate valid] at ready
      obtain ⟨rfl, rfl⟩ := ready
      obtain ⟨bounded, v, d⟩ := close_step_preserves values before after valid visible durable stepped
      exact .ok _ _ _ ⟨after, .inr rfl, bounded, v, d⟩


open Record.NamedRustlerRepair (nameBytes boot opened namespaceCell openingState opened_frame open_existing_prefix)
open Record.NamedJournalCrash (namedJournal inodeIds captured_journal)

/-- Both repair error and exhausted record limit close the borrowed journal
before the actual compiled caller returns or converts its failure. -/
private theorem typed_close_retains_journal (counter : Nat) (data : ByteArray) (choices rest : Term)
    (values : List U16) (maximum : U32) (positive : 1 ≤ counter)
    (bounded : data.size ≤ limit) (initial : LogImage values data)
    (reply : core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError)
    (closing : reply = .Ok none ∨ ∃ error, reply = .Err error)
    (middle after : Environment) (residual : Result Unit)
    (repair : Result.ReadyPrefix
      (repair_log ⟨counter + 1⟩ (UScalar.cast .Usize maximum)) (opened counter data choices rest)
      (.ok (reply, ⟨counter + 1⟩)) middle)
    (cleanup : Result.ReadyPrefix (NativeOwnedDrop.drop (⟨counter + 1⟩ : NativeFile))
      middle residual after) :
    JournalState 1 (boot counter data choices rest) ⟨counter + 1⟩
      [namespaceCell rest] values after ∧
    (residual = .ok () → lookup ⟨counter + 1⟩ after = none ∧
      pollClose ⟨counter + 1⟩ after = some (.error .exhausted, after)) ∧
    ∃ inside, Result.ReadyPrefix (__TRY_REOPEN__ maximum)
      (boot counter data choices rest) inside after := by
  have admitted : Admitted (openingState data choices) := ⟨bounded, bounded, Nat.zero_le _⟩
  have separate := opened_frame counter rest positive
  have safe := Record.RepairImageInvariant.repair_log_invariant (view := Record.FileView.named 1)
    (boot counter data choices rest) ⟨counter + 1⟩ [namespaceCell rest] values
    (openingState data choices) (UScalar.cast .Usize maximum)
    ((Record.FileView.named_separated 1 _ _).mpr separate) admitted rfl initial
  obtain ⟨state, equal, valid, visible, durable⟩ := (safe _ _ repair).1
  rw [Record.FileView.named_render] at equal
  subst middle
  refine ⟨(close_invariant 1 _ _ _ state values separate valid visible durable _ after cleanup).1, ?_, ?_⟩
  · intro done
    subst residual
    exact close_return_retires 1 _ _ state _ after separate valid cleanup
  rcases closing with rfl | ⟨error, rfl⟩
  all_goals
    simp only [__TRY_REOPEN__, monadLift_self, NativeM.lift, Result.ok_bind]
    apply Exists.intro
    apply Result.ReadyPrefix.bind
    simp only [shared_log.reopen, monadLift_self]
    apply Result.ReadyPrefix.trans ((open_existing_prefix counter data choices rest positive bounded).bind _)
    simp only [Result.ok_bind, core.result.Result.Insts.CoreOpsTry.branch, NativeM.monadLift_eq, NativeM.fromRust_ok]
    apply Result.ReadyPrefix.trans (repair.bind _)
    simpa only [Result.ok_bind] using cleanup.bind _


set_option maxRecDepth 8192 in
private theorem journal_capture (counter : Nat) (data : ByteArray) (choices rest : Term)
    (values : List U16) (world : Environment)
    (kept : JournalState 1 (boot counter data choices rest) ⟨counter + 1⟩ [namespaceCell rest] values world)
    (positive : 1 ≤ counter) (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks world = some image) :
    ∃ bytes, LogImage values bytes ∧ bytes.size ≤ limit ∧
      image = ⟨namedJournal nameBytes, [(1, bytes)], counter + 1⟩ := by
  obtain ⟨state, worldEq, valid, visible, durable⟩ := kept
  have one : 1 ≤ counter + 1 := by omega
  have nonzero : counter ≠ 0 := by omega
  have inodeValid : Admitted {state with position := 0, script := .nil} :=
    ⟨valid.1, valid.2.1, Nat.zero_le _⟩
  have counterValue : world.nativeRefCounter = counter + 1 := by
    rcases worldEq with rfl | rfl <;> simp only [closedWorld, namedWorld, boot] <;> omega
  have atNode : inode 1 world = some {state with position := 0, script := .nil} := by
    rcases worldEq with rfl | rfl
    · exact Record.FileView.named_inode 1 _ _ _ _ (opened_frame counter rest positive) valid
    · simp [closedWorld, namedWorld, boot, namespaceCell, inodeCell, inode, nonzero,
        not_lt.mpr one, List.filter_cons, List.filter_append, Record.ResizeProperties.decode_admitted _ inodeValid]
  have ids : inodeIds world = [1] := by
    rcases worldEq with rfl | rfl <;> simp only [inodeIds, closedWorld, namedWorld, boot, handleCell,
      inodeCell, namespaceCell, List.cons_append, List.nil_append, List.filter_cons] <;> rfl
  have namespaceEq : namespaceSnapshot world =
      some ⟨namedJournal nameBytes, namedJournal nameBytes, [], rest⟩ := by
    have supported : supportedPath nameBytes = true := by decide
    rcases worldEq with rfl | rfl <;> simp [closedWorld, namedWorld, boot, handleCell, namespaceCell, inodeCell,
      namespaceSnapshot, encodeNamespace, encodeNames, namespaceTable, namespaceHistory,
      namespaceEntry, List.eraseDups_cons, tablesEqual, namedJournal, supported]
  obtain ⟨mask, bytes, accepted, capture⟩ := captured_journal nameBytes world
    {state with position := 0, script := .nil} rest namespaceEq ids atNode chosen masks image crash
  have lengths := persist_lengths state.durable state.visible mask bytes accepted
  have durableBound := valid.2.1
  have visibleBound := valid.1
  rw [counterValue] at capture
  exact ⟨bytes, persist_log_image values _ _ _ _ durable visible accepted, by omega, capture⟩

/-- A crash while the actual typed NIF handles repair rejection or a failed
repair preserves the same acknowledged journal under every admitted close
and crash mask. The result carries the actual NIF prefix that reached it. -/
theorem typed_close_crash_preserves (counter : Nat) (data : ByteArray) (choices rest : Term)
    (values : List U16) (maximum : U32) (positive : 1 ≤ counter)
    (bounded : data.size ≤ limit) (initial : LogImage values data)
    (reply : core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError)
    (closing : reply = .Ok none ∨ ∃ error, reply = .Err error)
    (middle after : Environment) (residual : Result Unit)
    (repair : Result.ReadyPrefix
      (repair_log ⟨counter + 1⟩ (UScalar.cast .Usize maximum)) (opened counter data choices rest)
      (.ok (reply, ⟨counter + 1⟩)) middle)
    (cleanup : Result.ReadyPrefix (NativeOwnedDrop.drop (⟨counter + 1⟩ : NativeFile))
      middle residual after)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks after = some image) :
    ∃ inside bytes, Result.ReadyPrefix (__TRY_REOPEN__ maximum)
      (boot counter data choices rest) inside after ∧
      LogImage values bytes ∧ bytes.size ≤ limit ∧ image = ⟨namedJournal nameBytes, [(1, bytes)], counter + 1⟩ := by
  obtain ⟨safe, _, inside, reached⟩ :=
    typed_close_retains_journal counter data choices rest values maximum positive bounded initial
      reply closing middle after residual repair cleanup
  obtain ⟨bytes, state, bounded, captured⟩ :=
    journal_capture counter data choices rest values after safe positive chosen masks image crash
  exact ⟨inside, bytes, reached, state, bounded, captured⟩


/-- A completed consuming close inside the actual Rustler error or budget
rejection path retires its writable descriptor. The stale handle can neither
look up the file as an open capability nor close it again. -/
theorem typed_close_rejects_reuse (counter : Nat) (data : ByteArray) (choices rest : Term)
    (values : List U16) (maximum : U32) (positive : 1 ≤ counter)
    (bounded : data.size ≤ limit) (initial : LogImage values data)
    (reply : core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError)
    (closing : reply = .Ok none ∨ ∃ error, reply = .Err error) (middle after : Environment)
    (repair : Result.ReadyPrefix
      (repair_log ⟨counter + 1⟩ (UScalar.cast .Usize maximum)) (opened counter data choices rest)
      (.ok (reply, ⟨counter + 1⟩)) middle)
    (cleanup : Result.ReadyPrefix (NativeOwnedDrop.drop (⟨counter + 1⟩ : NativeFile))
      middle (.ok ()) after) :
    (∃ inside, Result.ReadyPrefix (__TRY_REOPEN__ maximum)
      (boot counter data choices rest) inside after) ∧
      lookup ⟨counter + 1⟩ after = none ∧
      pollClose ⟨counter + 1⟩ after = some (.error .exhausted, after) := by
  obtain ⟨_, retired, reached⟩ :=
    typed_close_retains_journal counter data choices rest values maximum positive bounded initial
      reply closing middle after _ repair cleanup
  exact ⟨reached, retired rfl⟩

end Record.NamedCloseInvariant
