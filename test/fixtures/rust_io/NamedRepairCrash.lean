module
public import Record.NamedRustlerRepair

public section

open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol

namespace Record.NamedRepairCrash
open NativeFile
open Record.FileView (namedWorld NamedSeparated named_inode named_render named_separated inodeCell handleCell)
open Record.NamedJournalCrash (namedJournal captured_journal inodeIds)
open Record.NamedRustlerRepair (nameBytes openScript namespaceCell openingState boot opened
  opened_frame open_existing_prefix arbitrary_repair_persists)
open Record.RepairCrashProperties (LogImage persist_lengths persist_log_image)
open Record.RepairImageInvariant (Reply snapshot repair_prefix_invariant)
open Record.ResizeProperties (Admitted)

private abbrev during (counter : Nat) (data : ByteArray) (choices rest : Term) (state : State) :
    Environment :=
  namedWorld 1 (boot counter data choices rest) ⟨counter + 1⟩ state [namespaceCell rest]

set_option maxRecDepth 8192 in
private theorem during_namespace (counter : Nat) (data : ByteArray) (choices rest : Term)
    (state : State) :
    namespaceSnapshot (during counter data choices rest state) =
      some ⟨namedJournal nameBytes, namedJournal nameBytes, [], rest⟩ := by
  have supported : supportedPath nameBytes = true := by decide
  simp [during, namedWorld, boot, handleCell, namespaceCell, inodeCell, namespaceSnapshot,
    encodeNamespace, encodeNames, namespaceTable, namespaceHistory, namespaceEntry, List.eraseDups_cons,
    tablesEqual, namedJournal, supported]

private theorem during_ids (counter : Nat) (data : ByteArray) (choices rest : Term)
    (state : State) : inodeIds (during counter data choices rest state) = [1] := by
  simp only [during, namedWorld, boot, inodeIds, handleCell, inodeCell, namespaceCell,
    List.cons_append, List.nil_append, List.filter_cons]
  rfl

/-- After opening a named descriptor, every finite prefix of the extracted repair
preserves the acknowledged records for all admitted file scripts and crash masks.
Only the filesystem image and allocator high-water mark enter the next boot. -/
theorem arbitrary_repair_prefix_crash (counter : Nat) (data : ByteArray) (choices rest : Term)
    (values : List U16) (maximum : Usize) (positive : 1 ≤ counter)
    (bounded : data.size ≤ limit) (initial : LogImage values data)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event) (last : Concurrent.Config Reply)
    (executed : Concurrent.Run (.start (opened counter data choices rest)
      (repair_log ⟨counter + 1⟩ maximum) elapsed) events last)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (snapshot (boot counter data choices rest).currentPid last) =
      some image) :
    ∃ bytes, LogImage values bytes ∧ bytes.size ≤ limit ∧
      image = ⟨namedJournal nameBytes, [(1, bytes)], counter + 1⟩ := by
  have separate := opened_frame counter rest positive
  have admitted : Admitted (openingState data choices) := ⟨bounded, bounded, Nat.zero_le _⟩
  have ran : Concurrent.Run (.start
      (@Record.FileView.render (Record.FileView.named 1) (boot counter data choices rest)
        ⟨counter + 1⟩ (openingState data choices) [namespaceCell rest])
      (repair_log ⟨counter + 1⟩ maximum) elapsed) events last := by
    simpa only [named_render, opened] using executed
  obtain ⟨state, equal, valid, visible, durable⟩ :=
    repair_prefix_invariant (view := Record.FileView.named 1)
      (boot counter data choices rest) ⟨counter + 1⟩ [namespaceCell rest] values
      (openingState data choices) maximum ((named_separated 1 _ _).mpr separate)
      admitted rfl initial elapsed events last ran
  rw [equal, named_render] at crash
  obtain ⟨mask, bytes, stored, captures⟩ :=
    captured_journal nameBytes (during counter data choices rest state)
      {state with position := 0, script := .nil} rest
      (during_namespace counter data choices rest state)
      (during_ids counter data choices rest state)
      (named_inode 1 _ _ _ _ separate valid) chosen masks image crash
  have lengths := persist_lengths state.durable state.visible mask bytes stored
  have durableBound := valid.2.1
  have visibleBound := valid.1
  have counterEq : (during counter data choices rest state).nativeRefCounter = counter + 1 := by
    simp only [during, namedWorld, boot]
    omega
  rw [counterEq] at captures
  exact ⟨bytes, persist_log_image values _ _ _ _ durable visible stored, by omega, captures⟩


/-- The stable name refers to one inode with a bounded acknowledged log image. -/
@[expose] def JournalImage (values : List U16) (image : FilesystemImage) : Prop :=
  1 ≤ image.highWater ∧ ∃ bytes, LogImage values bytes ∧ bytes.size ≤ limit ∧
    image = ⟨namedJournal nameBytes, [(1, bytes)], image.highWater⟩

/-- Each attempt starts after opening a descriptor from the previous disk image.
All subsequent repair steps and persistence masks come from the native model. -/
@[expose] def InterruptedRepair (before after : FilesystemImage) : Prop :=
  ∃ (bytes : ByteArray) (choices rest : Term) (maximum : Usize)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event) (last : Concurrent.Config Reply)
    (chosen : Names) (masks : List (Nat × ByteArray)),
    before = ⟨namedJournal nameBytes, [(1, bytes)], before.highWater⟩ ∧
    Concurrent.Run (.start (opened before.highWater bytes choices rest)
      (repair_log ⟨before.highWater + 1⟩ maximum) elapsed) events last ∧
    filesystemCrashImage chosen masks (snapshot (boot before.highWater bytes choices rest).currentPid last) =
      some after

inductive InterruptedRepairs : Nat → FilesystemImage → FilesystemImage → Prop where
  | zero : InterruptedRepairs 0 image image
  | next : InterruptedRepair before middle → InterruptedRepairs count middle after →
      InterruptedRepairs (count + 1) before after

theorem interrupted_preserves (values : List U16) (before after : FilesystemImage)
    (image : JournalImage values before) (attempt : InterruptedRepair before after) :
    JournalImage values after ∧ after.highWater = before.highWater + 1 := by
  obtain ⟨positive, start, valid, bounded, initial⟩ := image
  obtain ⟨bytes, choices, rest, maximum, elapsed, events, last, chosen, masks, started, ran, crash⟩ := attempt
  have imageEq := initial.symm.trans started
  have equal : start = bytes := by
    simpa only [FilesystemImage.mk.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] using imageEq
  subst start
  obtain ⟨kept, image, bounded, capture⟩ :=
    arbitrary_repair_prefix_crash before.highWater bytes choices rest values maximum positive bounded
      valid elapsed events last ran chosen masks after crash
  rw [capture]
  exact ⟨⟨by simp, kept, image, bounded, rfl⟩, rfl⟩

/-- Repeated crashes preserve every record and discard the newly opened file
handle each time. The high-water mark still advances once per admitted open. -/
theorem repeated_prefix_crashes (values : List U16) (before after : FilesystemImage) (count : Nat)
    (image : JournalImage values before) (attempts : InterruptedRepairs count before after) :
    JournalImage values after ∧ after.highWater = before.highWater + count := by
  induction attempts with
  | zero => exact ⟨image, by simp⟩
  | @next before middle count after first rest ih =>
    obtain ⟨mid, advance⟩ := interrupted_preserves values before middle image first
    obtain ⟨kept, later⟩ := ih mid
    exact ⟨kept, by omega⟩

/-- Register the configured type after booting the exact captured filesystem
image. No descriptor, resource or lock cell survives the restart. -/
@[expose] def registerLog (env : Environment) : Environment :=
  {env with nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource]}

set_option maxRecDepth 8192 in
theorem boot_from_image (counter : Nat) (bytes : ByteArray) (choices rest : Term)
    (positive : 1 ≤ counter) (bounded : bytes.size ≤ limit) :
    (restartFilesystem ⟨namedJournal nameBytes, [(1, bytes)], counter⟩
      (openScript choices rest)).map registerLog = some (boot counter bytes choices rest) := by
  have supported : supportedPath nameBytes = true := by decide
  simp [restartFilesystem, namespaceTable, namespaceEntry, encodeNames,
    List.eraseDups_cons, namedJournal, supported, not_lt.mpr positive, not_lt.mpr bounded,
    boot, registerLog, openingState, namespaceCell, inodeCell]

/-- A captured disk after arbitrarily many interrupted workspace repairs can be
booted into the actual compiled Rustler binding. Every successful retry restores
the exact synchronized record encoding for every admitted next power loss. -/
theorem typed_retry_after_prefix_crashes (values : List U16) (before after : FilesystemImage)
    (count : Nat) (image : JournalImage values before) (attempts : InterruptedRepairs count before after) :
    ∃ bytes, after.highWater = before.highWater + count ∧
      ∀ (choices rest : Term), (restartFilesystem after (openScript choices rest)).map registerLog =
        some (boot after.highWater bytes choices rest) ∧
        Result.ReadyPrefix (io_protocol.open_readwrite (toStr "journal"))
          (boot after.highWater bytes choices rest) (.ok (.Ok ⟨after.highWater + 1⟩))
          (opened after.highWater bytes choices rest) ∧
        ∀ (maximum : U32) (owner : NativeResourceArc shared_log.LogResource) (world : Environment),
          Result.ReadyPrefix (__TRY_REOPEN__ maximum)
            (boot after.highWater bytes choices rest) (.ok (.Ok owner)) world →
          ∀ (chosen : Names) (masks : List (Nat × ByteArray)) (next : FilesystemImage),
            filesystemCrashImage chosen masks world = some next →
            next = ⟨namedJournal nameBytes, [(1, Record.CrashProperties.disk (Record.LogProperties.logBytes values))],
              before.highWater + count + 4⟩ := by
  obtain ⟨⟨positive, bytes, kept, bounded, captured⟩, advance⟩ :=
    repeated_prefix_crashes values before after count image attempts
  refine ⟨bytes, advance, fun choices rest => ⟨?_, open_existing_prefix _ _ _ _ positive bounded, ?_⟩⟩
  · have booted := boot_from_image after.highWater bytes choices rest positive bounded
    simpa only [← captured] using booted
  · intro maximum owner world trace chosen masks next crash
    simpa only [advance] using
      arbitrary_repair_persists after.highWater bytes choices rest values maximum positive bounded
        kept owner world trace chosen masks next crash


/-- A real ready prefix of repair is reachable inside the compiled typed
Rustler call, after its compiled open and before allocation or cleanup. -/
private theorem typed_contains_repair_prefix (counter : Nat) (bytes : ByteArray) (choices rest : Term)
    (maximum : U32) (positive : 1 ≤ counter) (bounded : bytes.size ≤ limit)
    (residual : Result Reply) (after : Environment)
    (trace : Result.ReadyPrefix (repair_log ⟨counter + 1⟩ (UScalar.cast .Usize maximum))
      (opened counter bytes choices rest) residual after) :
    ∃ inside, Result.ReadyPrefix (__TRY_REOPEN__ maximum)
      (boot counter bytes choices rest) inside after := by
  simp only [__TRY_REOPEN__, monadLift_self, NativeM.lift,
    Result.ok_bind]
  apply Exists.intro
  apply Result.ReadyPrefix.bind
  simp only [shared_log.reopen, monadLift_self]
  have starts := open_existing_prefix counter bytes choices rest positive bounded
  apply Result.ReadyPrefix.trans (starts.bind _)
  simp only [Result.ok_bind, core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq, NativeM.fromRust_ok]
  exact trace.bind _


/-- Every finite workspace repair run, including a blocked wait, exposes the
same crash environment at a ready prefix of the actual compiled typed NIF. -/
private theorem typed_reaches_repair_snapshot (counter : Nat) (data : ByteArray) (choices rest : Term)
    (values : List U16) (maximum : U32) (positive : 1 ≤ counter)
    (bounded : data.size ≤ limit) (initial : LogImage values data)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event) (last : Concurrent.Config Reply)
    (executed : Concurrent.Run (.start (opened counter data choices rest)
      (repair_log ⟨counter + 1⟩ (UScalar.cast .Usize maximum)) elapsed) events last) :
    ∃ inside, Result.ReadyPrefix (__TRY_REOPEN__ maximum)
      (boot counter data choices rest) inside (snapshot (boot counter data choices rest).currentPid last) := by
  have admitted : Admitted (openingState data choices) := ⟨bounded, bounded, Nat.zero_le _⟩
  have separate := (named_separated 1 _ _).mpr (opened_frame counter rest positive)
  have safe := Record.RepairImageInvariant.repair_log_invariant (view := Record.FileView.named 1)
    (boot counter data choices rest) ⟨counter + 1⟩ [namespaceCell rest] values
    (openingState data choices) (UScalar.cast .Usize maximum) separate admitted rfl initial
  obtain ⟨world, residual, trace, ending⟩ := safe.run_prefix elapsed executed
  have exposed := typed_contains_repair_prefix counter data choices rest maximum positive bounded residual world trace
  rcases ending with rfl | rfl
  · simpa only [snapshot] using exposed
  · obtain ⟨state, rfl, _, _, _⟩ := (safe residual world trace).1
    have same := @Record.FileView.initial_view (Record.FileView.named 1)
      (boot counter data choices rest) ⟨counter + 1⟩ state [namespaceCell rest] elapsed
    simpa only [snapshot, same] using exposed


/-- The captured state is reachable in the actual typed NIF and retains the
acknowledged bytes. This ranges over every repair prefix reached between
successful descriptor open and the caller's return handling. -/
theorem typed_repair_prefix_crash (counter : Nat) (data : ByteArray) (choices rest : Term)
    (values : List U16) (maximum : U32) (positive : 1 ≤ counter)
    (bounded : data.size ≤ limit) (initial : LogImage values data)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event) (last : Concurrent.Config Reply)
    (executed : Concurrent.Run (.start (opened counter data choices rest)
      (repair_log ⟨counter + 1⟩ (UScalar.cast .Usize maximum)) elapsed) events last)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (snapshot (boot counter data choices rest).currentPid last) =
      some image) :
    ∃ inside bytes, Result.ReadyPrefix (__TRY_REOPEN__ maximum)
      (boot counter data choices rest) inside (snapshot (boot counter data choices rest).currentPid last) ∧
      LogImage values bytes ∧ bytes.size ≤ limit ∧
      image = ⟨namedJournal nameBytes, [(1, bytes)], counter + 1⟩ := by
  obtain ⟨inside, reached⟩ := typed_reaches_repair_snapshot counter data choices rest values maximum
    positive bounded initial elapsed events last executed
  obtain ⟨bytes, kept, length, captured⟩ := arbitrary_repair_prefix_crash counter data choices rest values
    (UScalar.cast .Usize maximum) positive bounded initial elapsed events last executed chosen masks image crash
  exact ⟨inside, bytes, reached, kept, length, captured⟩

end Record.NamedRepairCrash
