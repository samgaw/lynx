module
public import Record.ReopenedLogProperties
public import Record.RepeatedRepairProperties
import Lynx.Runner.NativeArithmetic
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.ReopenedRepairPrefix
open NativeFile Record.ReopenedLogProperties Record.RepairCrashProperties
  Record.CrashProperties Record.LogProperties

@[expose] def script (sync : Term) : Term :=
  .cons (.tuple #[.atom "open", .bitstring fileName 0, .atom "ok", .integer 0, sync]) .nil

open scoped Lynx.NativeArithmetic
open Record.RepeatedRepairProperties (repairScript interruptionScript)
open Record.RecoveryProperties (zeroMask)

@[expose] def reopenScript (bytes : ByteArray) (syncs : Bool) : Term :=
  script (if syncs then repairScript bytes .nil else interruptionScript bytes (zeroMask bytes) .nil)

@[expose] def cold (counter : Nat) (bytes : ByteArray) (syncs : Bool) : Environment := {
  nativeRefCounter := counter
  nativeHeap := [
    (0, namespaceTypeName, encodeNamespace ⟨names, names, [], reopenScript bytes syncs⟩),
    (1, inodeTypeName, encode ⟨bytes, bytes, 0, .nil⟩)] }

@[expose] def registered (env : Environment) : Environment :=
  {env with nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource]}

@[expose] def start (syncs : Bool) : Environment := registered (cold 1 torn syncs)

@[expose] def finish (reopen : U32 → NativeM (NativeResourceArc shared_log.LogResource)) :
    Result Term := do
  let owner ← reopen 2#u32
  let term ← NativeResourceArc.encode owner
  NativeOwnedDrop.drop owner
  Result.ok term

@[expose] def inodeIds (env : Environment) : List Nat :=
  (env.nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName)).map Prod.fst

@[expose] def retainedBytes (bytes : ByteArray) : Bool :=
  repaired.size ≤ bytes.size && bytes.size < repaired.size + 4 &&
    (List.range repaired.size).all (fun index => bytes[index]! == repaired[index]!)

@[expose] def retained (counter : Nat) (config : Concurrent.Config Term) : Bool :=
  let env := finalEnvironment config
  counter ≤ env.nativeRefCounter && inodeIds env == [1] &&
  (match namespaceSnapshot env with
   | some table => tablesEqual table.names names && tablesEqual table.committed names && table.pending.isEmpty
   | none => false) &&
  (match inode 1 env with
   | some disk => retainedBytes disk.visible && retainedBytes disk.durable
   | none => false)

/-- The interrupted case reaches the synchronization wait with the repaired
visible prefix, the old durable bytes and no returned resource. -/
@[expose] def stoppedBeforeSync (config : Concurrent.Config Term) : Bool :=
  match config.outcome, inode 1 (finalEnvironment config) with
  | .deadlock, some disk =>
    disk.visible.data == repaired.data && disk.durable.data == torn.data &&
      (finalEnvironment config).nativeRefCounter == 2
  | _, _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem blocked_sync_checked (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost stoppedBeforeSync 64
      (.start (start false) (finish __REOPEN__) elapsed) = true := by
  set_option cbv.maxSteps 32000000 in cbv

private theorem tail_forms (tail : List U8) (short : tail.length < 4) :
    tail = [] ∨ (∃ a, tail = [a]) ∨ (∃ a b, tail = [a, b]) ∨ (∃ a b c, tail = [a, b, c]) := by
  cases tail with
  | nil => exact .inl rfl
  | cons first rest =>
    cases rest with
    | nil => exact .inr (.inl ⟨first, rfl⟩)
    | cons second rest =>
      cases rest with
      | nil => exact .inr (.inr (.inl ⟨first, second, rfl⟩))
      | cons third rest =>
        cases rest with
        | nil => exact .inr (.inr (.inr ⟨first, second, third, rfl⟩))
        | cons fourth rest =>
          simp only [List.length_cons] at short
          omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
theorem restart_prefixes_checked (counter : Nat) (bytes : ByteArray)
    (positive : 1 ≤ counter) (shape : LogImage [13#u16] bytes)
    (syncs : Bool) (elapsed : PID → Nat → Nat) :
    restartFilesystem ⟨names, [(1, bytes)], counter⟩ (reopenScript bytes syncs) =
      some (cold counter bytes syncs) ∧
    Concurrent.checkInvariant (retained counter) 64
      (.start (registered (cold counter bytes syncs)) (finish __REOPEN__) elapsed) = true := by
  obtain ⟨tail, short, rfl⟩ := log_image_shape [13#u16] bytes shape
  rcases tail_forms tail short with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    cases syncs <;> constructor <;> cbv

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

private theorem selected_is_journal (selected : Names) (script : Term)
    (unique : (selected.map (fun entry => entry.1.data)).eraseDups.length = selected.length)
    (allowed : namespaceCrashAllowed ⟨names, names, [], script⟩ selected = true) :
    selected = names := by
  simp [namespaceCrashAllowed, names, namedInode] at allowed
  have mapped : selected.map (fun entry => entry.1.data) =
      List.replicate selected.length fileName.data := by
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
    have same : head.1 = fileName :=
      ByteArray.ext (allowed.1 head.1 head.2 (by simp)).symm
    obtain ⟨path, node⟩ := head
    simp only at same
    subst path
    simp at found
    simp [names, found]

private theorem one_inode {α : Type} (items : List α) (tag : α → Nat)
    (ids : items.map tag = [1]) : ∃ node, items = [node] ∧ tag node = 1 := by
  cases items with
  | nil => simp at ids
  | cons node rest =>
    simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at ids
    exact ⟨node, by simp [ids.2], ids.1⟩

private theorem captured_journal (env : Environment) (disk : State) (script : Term)
    (tables : namespaceSnapshot env = some ⟨names, names, [], script⟩)
    (ids : inodeIds env = [1]) (found : inode 1 env = some disk)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks env = some image) :
    ∃ mask bytes, persist disk.durable disk.visible mask = some bytes ∧
      image = ⟨names, [(1, bytes)], env.nativeRefCounter⟩ := by
  unfold inodeIds at ids
  obtain ⟨node, nodes, nodeId⟩ := one_inode _ _ ids
  unfold filesystemCrashImage at crash
  rw [tables] at crash
  simp only [Bind.bind, Option.bind_some, Option.bind_eq_some_iff] at crash
  obtain ⟨selected, normalized, crash⟩ := crash
  split at crash
  · contradiction
  · rename_i allowed
    have permit : namespaceCrashAllowed ⟨names, names, [], script⟩ selected = true := by
      simpa using allowed
    have selectedNames := selected_is_journal selected script
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
        simp [choice, names] at crash
        exact ⟨mask, bytes, by simp [choice], crash.symm⟩

private theorem repaired_bytes : repaired = disk (logBytes [13#u16]) := by decide +kernel

private theorem bytes_protected (bytes : ByteArray) (allowed : retainedBytes bytes = true) :
    LogImage [13#u16] bytes := by
  simp only [retainedBytes, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at allowed
  obtain ⟨⟨lower, upper⟩, checked⟩ := allowed
  unfold LogImage Prefix
  rw [← repaired_bytes]
  refine ⟨⟨lower, ?_⟩, upper⟩
  intro i inside
  exact checked i (List.mem_range.mpr inside)

private theorem names_equal (left right : NativeFile.Names)
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

private theorem captured_from_retained (counter : Nat) (config : Concurrent.Config Term)
    (safe : retained counter config = true) (chosen : Names) (masks : List (Nat × ByteArray))
    (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (finalEnvironment config) = some image) :
    ∃ bytes, image = ⟨names, [(1, bytes)], (finalEnvironment config).nativeRefCounter⟩ ∧
      counter ≤ image.highWater ∧ LogImage [13#u16] bytes := by
  unfold retained at safe
  dsimp only at safe
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at safe
  obtain ⟨⟨⟨positive, ids⟩, table⟩, contents⟩ := safe
  split at table
  · rename_i snapshot tables
    simp only [Bool.and_eq_true, List.isEmpty_iff] at table
    obtain ⟨⟨visible, committed⟩, pending⟩ := table
    have fixed : namespaceSnapshot (finalEnvironment config) =
        some ⟨names, names, [], snapshot.script⟩ := by
      rw [tables]
      have named := names_equal _ _ visible
      have stable := names_equal _ _ committed
      cases snapshot
      simp_all
    split at contents
    · rename_i disk found
      simp only [Bool.and_eq_true] at contents
      obtain ⟨mask, bytes, accepted, same⟩ :=
        captured_journal _ disk snapshot.script fixed ids found chosen masks image crash
      have v := bytes_protected _ contents.1
      have d := bytes_protected _ contents.2
      exact ⟨bytes, same, by simpa [same] using positive,
        persist_log_image _ _ _ _ _ d v accepted⟩
    · contradiction
  · contradiction

@[expose] def repairState (counter eof : Nat) (env : Environment) : Bool :=
  match lookup ⟨counter + 1⟩ env, namespaceSnapshot env with
  | some file, some table =>
    let payload : shared_log.LogResource := ⟨⟨counter + 2⟩⟩
    env.nativeRefCounter == counter + 6 &&
    file.visible.data == repaired.data && file.durable.data == repaired.data &&
    file.position == eof && file.script == .nil &&
    (NativeResourceArc.vmCells payload (counter + 3) (counter + 5) (counter + 6)).all
      (fun cell => env.nativeHeap.contains cell) &&
    !env.nativeHeap.any (fun cell => cell.1 == counter + 4) &&
    env.nativeHeap.contains (counter + 2, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference (counter + 1)]) &&
    namedInode table.names fileName == some 1 && namedInode table.committed fileName == some 1
  | _, _ => false

@[expose] def completedRepair (counter eof : Nat) (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.nativeReference pin) => pin == counter + 6 && repairState counter eof (finalEnvironment config)
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
/-- Every bounded byte tail that can survive the interrupted repair can be
reopened by the actual compiled Rustler NIF under the successful host script. -/
theorem named_retry_checked (counter : Nat) (bytes : ByteArray)
    (positive : 1 ≤ counter) (shape : LogImage [13#u16] bytes)
    (elapsed : PID → Nat → Nat) :
    restartFilesystem ⟨names, [(1, bytes)], counter⟩
      (reopenScript bytes true) = some (cold counter bytes true) ∧
    Concurrent.checkPost (completedRepair counter bytes.size) 64
      (.start (registered (cold counter bytes true)) (finish __REOPEN__) elapsed) = true := by
  obtain ⟨tail, short, rfl⟩ := log_image_shape [13#u16] bytes shape
  rcases tail_forms tail short with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    constructor <;> cbv

/-- The synchronized name refers to the one inode whose bytes still contain
the acknowledged record. The counter is ghost freshness bookkeeping. -/
@[expose] def JournalImage (image : FilesystemImage) : Prop :=
  ∃ bytes, image = ⟨names, [(1, bytes)], image.highWater⟩ ∧
    LogImage [13#u16] bytes ∧ 1 ≤ image.highWater

/-- One witnessed execution after reboot, followed by any admitted crash.
The run can stop before, during, or after synchronization. -/
@[expose] def CrashAttempt
    (reopen : U32 → NativeM (NativeResourceArc shared_log.LogResource))
    (before after : FilesystemImage) : Prop :=
  ∃ bytes syncs boot elapsed events last chosen masks,
    before = ⟨names, [(1, bytes)], before.highWater⟩ ∧
    restartFilesystem before (reopenScript bytes syncs) = some boot ∧
    Concurrent.Run (.start (registered boot) (finish reopen) elapsed) events last ∧
    filesystemCrashImage chosen masks (finalEnvironment last) = some after

inductive CrashAttempts
    (reopen : U32 → NativeM (NativeResourceArc shared_log.LogResource)) :
    Nat → FilesystemImage → FilesystemImage → Prop where
  | zero : CrashAttempts reopen 0 image image
  | next : CrashAttempt reopen before middle → CrashAttempts reopen n middle after →
      CrashAttempts reopen (n + 1) before after

private theorem one_crash (before after : FilesystemImage) (valid : JournalImage before)
    (attempt : CrashAttempt __REOPEN__ before after) :
    JournalImage after ∧ before.highWater ≤ after.highWater := by
  obtain ⟨bytes, represented, shape, positive⟩ := valid
  obtain ⟨input, syncs, boot, elapsed, events, last, chosen, masks, givenImage, restarted, run, crash⟩ := attempt
  have equal : input = bytes := by
    simpa using congrArg FilesystemImage.inodes (givenImage.symm.trans represented)
  subst input
  obtain ⟨coldRestart, checked⟩ := restart_prefixes_checked before.highWater bytes positive shape syncs elapsed
  rw [represented] at restarted
  have sameBoot := Option.some.inj (restarted.symm.trans coldRestart)
  subst boot
  obtain ⟨persisted, image, advances, keeps⟩ :=
    captured_from_retained before.highWater last (Concurrent.checkInvariant_sound checked run)
      chosen masks after crash
  have counter : after.highWater = (finalEnvironment last).nativeRefCounter := by rw [image]
  exact ⟨⟨persisted, by rw [counter]; exact image, keeps, Nat.le_trans positive advances⟩, advances⟩

/-- Any finite chain of actual interrupted Rustler reopen calls preserves the
acknowledged record and admits a subsequent actual successful repair with
a fresh VM pin. The final successful I/O script remains a host premise. -/
theorem retry_after_crashes (count : Nat) (before after : FilesystemImage)
    (valid : JournalImage before)
    (attempts : CrashAttempts __REOPEN__ count before after) :
    before.highWater ≤ after.highWater ∧
    ∃ bytes boot,
      after = ⟨names, [(1, bytes)], after.highWater⟩ ∧ LogImage [13#u16] bytes ∧
      restartFilesystem after (reopenScript bytes true) = some boot ∧
      ∀ elapsed events last outcome,
        Concurrent.Run (.start (registered boot) (finish __REOPEN__) elapsed) events last →
        Concurrent.Terminal last outcome →
        completedRepair after.highWater bytes.size last = true := by
  have retained : JournalImage after ∧ before.highWater ≤ after.highWater := by
    induction attempts with
    | zero => exact ⟨valid, Nat.le_refl _⟩
    | next head _ ih =>
      obtain ⟨kept, advanced⟩ := one_crash _ _ valid head
      obtain ⟨remains, advances⟩ := ih kept
      exact ⟨remains, Nat.le_trans advanced advances⟩
  obtain ⟨⟨bytes, image, shape, high⟩, evolved⟩ := retained
  have boot := (named_retry_checked after.highWater bytes high shape (fun _ _ => 0)).1
  refine ⟨evolved, bytes, cold after.highWater bytes true, image, shape, ?_, ?_⟩
  · rw [image]
    exact boot
  · intro elapsed events last outcome run terminal
    exact Concurrent.checkPost_sound
      (named_retry_checked after.highWater bytes high shape elapsed).2 run terminal

@[expose] def blockedImage : FilesystemImage := ⟨names, [(1, torn)], 2⟩

@[expose] def recoveredBoot : Environment := registered (cold 2 torn true)

@[expose] def captureBlocked (config : Concurrent.Config Term) : Option FilesystemImage :=
  filesystemCrashImage names [(1, zeros6)] (finalEnvironment config)

@[expose] def capturedOldImage (config : Concurrent.Config Term) : Bool :=
  match captureBlocked config with
  | some ⟨selected, [(1, bytes)], counter⟩ =>
    tablesEqual selected names && bytes.data == torn.data && counter == 2
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
private theorem capture_checked :
    Concurrent.checkPost capturedOldImage 64 (.start (start false) (finish __REOPEN__)) = true := by
  cbv

/-- The modeled adapter's new boot is reachable after a crash at the actual
blocked synchronization. This witness retains the complete old durable image. -/
theorem blocked_reboot_witness :
    (∃ events last, Concurrent.Run (.start (start false) (finish __REOPEN__)) events last ∧
      Concurrent.Terminal last .deadlock ∧ captureBlocked last = some blockedImage) ∧
    restartFilesystem blockedImage (reopenScript torn true) =
      some (cold 2 torn true) := by
  constructor
  · obtain ⟨events, last, run, terminal⟩ :=
      Result.run_reaches (finish __REOPEN__) (start false) []
    have stopped := Concurrent.checkPost_sound (blocked_sync_checked (fun _ _ => 0)) run terminal
    have outcome : last.outcome = .deadlock := by
      unfold stoppedBeforeSync at stopped
      split at stopped
      · assumption
      · contradiction
    have crash := Concurrent.checkPost_sound capture_checked run terminal
    have captured : captureBlocked last = some blockedImage := by
      unfold capturedOldImage at crash
      split at crash
      · rename_i selected bytes counter saved
        simp only [Bool.and_eq_true, beq_iff_eq] at crash
        obtain ⟨⟨directory, image⟩, sameCounter⟩ := crash
        rw [saved, names_equal _ _ directory, ByteArray.ext image, sameCounter]
        rfl
      · contradiction
    refine ⟨events, last, run, ?_, captured⟩
    rw [terminal.outcome_eq] at outcome
    simpa only [outcome] using terminal
  · exact (named_retry_checked 2 torn (by decide) (bytes_protected torn (by decide)) (fun _ _ => 0)).1

@[expose] def recoveryLaw (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.atom "true") => repairState 2 torn.size (finalEnvironment config)
  | _ => false

theorem recovery_law_outcome (config : Concurrent.Config Term)
    (accepted : recoveryLaw config = true) : config.outcome = .ok Term.true := by
  unfold recoveryLaw at accepted
  split at accepted
  · assumption
  · contradiction

end Record.ReopenedRepairPrefix
