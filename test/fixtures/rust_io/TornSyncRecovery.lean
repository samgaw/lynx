module
public import Record.TornSyncFailure
import Lynx.Runner.NativeArithmetic

public section

open Aeneas Aeneas.Std Lynx io_native

namespace Record.TornSyncRecovery
open NativeFile
open scoped Lynx.NativeArithmetic
open Record.FallibleReopen (journalName call contents environment openScript)
open Record.NamedJournalCrash (namedJournal JournalBytes inodeIds names_equal captured_journal persist_journal)
open Record.TornSyncFailure (withTail choose zeros rejected preserves boot
  failed_sync_preserves_acknowledgements failedSyncBoot)

@[expose] def names : Names := namedJournal journalName

private theorem contents_size (left : Bool) : (contents left).size = 8 := by
  cases left <;> rfl

private theorem durable_prefix (left : Bool) (data : ByteArray)
    (preserved : preserves left data = true) : JournalBytes (contents left) data := by
  simp only [preserves, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at preserved
  rw [JournalBytes, contents_size]
  exact ⟨⟨preserved.1.1, preserved.2⟩, preserved.1.2⟩

/-- After the typed sync error and cleanup, every admitted filesystem crash
retains the two complete records and the synchronized journal name. -/
private theorem capture_after_failure (counter : Nat) (left : Bool) (tailLength closeTail : Nat)
    (last : Concurrent.Config Term) (failure : rejected counter left tailLength closeTail last = true)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (environment last) = some image) :
    ∃ data, image = ⟨names, [(1, data)], counter + 2⟩ ∧ JournalBytes (contents left) data := by
  unfold rejected at failure
  dsimp only at failure
  split at failure
  · rename_i file table descriptor outcome found snapshot closed
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at failure
    have visible : file.visible = contents left := ByteArray.ext (by tauto)
    have durable : JournalBytes (contents left) file.durable := durable_prefix _ _ (by tauto)
    have current : JournalBytes (contents left) file.visible := by
      rw [visible]
      exact ⟨⟨le_rfl, fun _ _ => rfl⟩, by omega⟩
    have named : namespaceSnapshot (environment last) = some ⟨names, names, [], table.script⟩ := by
      rw [snapshot]
      have live : table.names = names := names_equal _ _ (by tauto)
      have stable : table.committed = names := names_equal _ _ (by tauto)
      have pending : table.pending = [] := by tauto
      cases table
      simp_all
    have ids : inodeIds (environment last) = [1] := by tauto
    have high : (environment last).nativeRefCounter = counter + 2 := by tauto
    obtain ⟨mask, kept, accepted, captured⟩ :=
      captured_journal journalName _ file table.script named ids found chosen masks image crash
    exact ⟨kept, captured.trans (by rw [high]; rfl), persist_journal _ _ _ _ _ durable current accepted⟩
  · contradiction

private theorem image_shape (left : Bool) (data : ByteArray)
    (shape : JournalBytes (contents left) data) :
    ∃ tail : List UInt8, tail.length < 4 ∧ data = withTail left tail := by
  let head := contents left
  have equal : data.data.toList.take head.size = head.data.toList := by
    apply List.ext_getElem
    · simp only [List.length_take, _root_.Array.length_toList, ← ByteArray.size_data]
      exact Nat.min_eq_left shape.1.1
    · intro i _ hj
      have inside : i < head.size := by simpa only [_root_.Array.length_toList, ← ByteArray.size_data] using hj
      have bytes := shape.1.2 i inside
      have bound : head.size ≤ data.size := shape.1.1
      rw [getElem!_pos data i (Nat.lt_of_lt_of_le inside bound), getElem!_pos head i inside] at bytes
      simpa only [List.getElem_take, _root_.Array.getElem_toList, ByteArray.getElem_eq_getElem_data] using bytes
  let tail := data.data.toList.drop head.size
  refine ⟨tail, ?_, ?_⟩
  · simp only [tail, List.length_drop, _root_.Array.length_toList, ← ByteArray.size_data]
    change data.size - head.size < 4
    have bound : data.size < head.size + 4 := shape.2
    omega
  · apply ByteArray.ext
    apply _root_.Array.toList_inj.mp
    have reconstructed := List.take_append_drop head.size data.data.toList
    rw [equal] at reconstructed
    simpa [withTail, head, tail] using reconstructed.symm

@[expose] def script (data : ByteArray) : Term :=
  let mask := zeros data.size
  let finished := choose "read" true 0 mask
    (choose "set_len" true 0 mask (choose "sync_all" true 0 ByteArray.empty .nil))
  openScript true 0 (choose "seek" true 0 mask
    ((List.range data.size).foldr (fun _ => choose "read" true 1 mask) finished)) .nil

@[expose] def cold (counter : Nat) (data : ByteArray) : Environment := {
  nativeRefCounter := counter
  nativeHeap := [
    (0, namespaceTypeName, encodeNamespace ⟨names, names, [], script data⟩),
    (1, inodeTypeName, encode ⟨data, data, 0, .nil⟩)] }

@[expose] def registered (env : Environment) : Environment :=
  {env with nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource]}

@[expose] def repaired (counter : Nat) (left : Bool) (eof : Nat)
    (last : Concurrent.Config Term) : Bool :=
  let env := environment last
  match last.outcome, getHandle ⟨counter + 1⟩ writableHandleTypeName env,
      inode 1 env, namespaceSnapshot env with
  | .ok (.nativeReference pin), some handle, some file, some table =>
    let payload : shared_log.LogResource := ⟨⟨counter + 2⟩⟩
    pin == counter + 6 && env.nativeRefCounter == pin &&
    handle.inode == 1 && handle.position == eof && handle.script == .nil &&
    file.visible.data == (contents left).data && file.durable.data == (contents left).data &&
    tablesEqual table.names names && tablesEqual table.committed names &&
    table.pending.isEmpty && table.script == .nil && inodeIds env == [1] &&
    (NativeResourceArc.vmCells payload (counter + 3) (counter + 5) pin).all env.nativeHeap.contains &&
    env.nativeHeap.contains (counter + 2, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference (counter + 1)]) &&
    !env.nativeHeap.any (fun cell => cell.1 == counter + 4)
  | _, _, _, _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 64000000 in
/-- A successful typed reopen after restart strips every possible short tail,
restores both acknowledged records, and returns a fresh writable VM pin. -/
theorem reopens_captured_image (counter : Nat) (left : Bool) (data : ByteArray)
    (positive : 1 ≤ counter) (shape : JournalBytes (contents left) data) (elapsed : PID → Nat → Nat) :
    restartFilesystem ⟨names, [(1, data)], counter⟩ (script data) = some (cold counter data) ∧
    Concurrent.checkPost (repaired counter left data.size) 64
      (.start (registered (cold counter data))
        (call __TRY_REOPEN__ 3#u32) elapsed) = true := by
  obtain ⟨tail, short, rfl⟩ := image_shape left data shape
  rcases Record.TornSyncFailure.tail_forms tail short with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    cases left <;> constructor <;> cbv

/-- Any admitted crash after the typed synchronization failure retains the same
two records. A successful host script on that exact reboot image lets the same
compiled NIF repair it and return a fresh writable resource. -/
theorem failed_sync_crash_reopens (counter : Nat) (left : Bool)
    (tail : List UInt8) (short : tail.length < 4) (syncTail closeTail : Fin 4)
    (syncBound : syncTail.val ≤ tail.length) (closeBound : closeTail.val ≤ syncTail.val)
    (closeSucceeds : Bool) (positive : 1 ≤ counter)
    (elapsed afterElapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term) (outcome : Lynx.Outcome Term)
    (run : Concurrent.Run
      (.start (boot counter left tail syncTail.val closeTail.val closeSucceeds)
        (call __TRY_REOPEN__ 3#u32) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (environment last) = some image) :
    ∃ data, image = ⟨names, [(1, data)], counter + 2⟩ ∧ JournalBytes (contents left) data ∧
      restartFilesystem image (script data) = some (cold (counter + 2) data) ∧
      Concurrent.checkPost (repaired (counter + 2) left data.size) 64
        (.start (registered (cold (counter + 2) data))
          (call __TRY_REOPEN__ 3#u32) afterElapsed) = true := by
  have failure :=
    Concurrent.checkPost_sound
      (failed_sync_preserves_acknowledgements counter left tail short syncTail closeTail syncBound
        closeBound closeSucceeds positive elapsed) run terminal
  obtain ⟨data, same, bytes⟩ :=
    capture_after_failure counter left tail.length closeTail.val last failure chosen masks image crash
  have reopened := reopens_captured_image (counter + 2) left data (by omega) bytes afterElapsed
  exact ⟨data, same, bytes, by simpa only [same] using reopened.1, reopened.2⟩

@[expose] def restartImage : FilesystemImage :=
  ⟨names, [(1, withTail true [99])], 3⟩

@[expose] def witnessMask : List (Nat × ByteArray) :=
  [(1, ⟨#[1,0,1,0,1,0,1,0,0]⟩)]

@[expose] def retryBoot : Environment := registered (cold 3 (withTail true [99]))

private def capturesRestart (last : Concurrent.Config Term) : Bool :=
  match filesystemCrashImage names witnessMask (environment last) with
  | some image =>
    match image.inodes with
    | [(1, data)] =>
      tablesEqual image.names names && data.data == (withTail true [99]).data &&
      image.highWater == 3
    | _ => false
  | none => false

private theorem captured_restart (last : Concurrent.Config Term)
    (checked : capturesRestart last = true) :
    filesystemCrashImage names witnessMask (environment last) = some restartImage := by
  unfold capturesRestart at checked
  split at checked
  · rename_i image admission
    split at checked
    · rename_i data selected
      simp only [Bool.and_eq_true, beq_iff_eq] at checked
      obtain ⟨⟨named, bytes⟩, high⟩ := checked
      rw [admission]
      cases image
      simp_all only [restartImage, ByteArray.ext bytes, Option.some.injEq]
      rw [Record.NamedJournalCrash.names_equal _ _ named]
    · contradiction
  · contradiction

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
/-- A mixed byte mask after the actual failed sync reaches the cold state
used by the Elixir restart law. No live owner from the failed attempt is reused. -/
theorem reboot_witness :
    (∃ events last outcome,
      Concurrent.Run (.start failedSyncBoot
        (call __TRY_REOPEN__ 3#u32)) events last ∧
      Concurrent.Terminal last outcome ∧
      filesystemCrashImage names witnessMask (environment last) = some restartImage) ∧
    (restartFilesystem restartImage (script (withTail true [99]))).map registered = some retryBoot := by
  constructor
  · have checked :
        Concurrent.checkPost capturesRestart 64 (.start failedSyncBoot
          (call __TRY_REOPEN__ 3#u32)) = true := by
      cbv
    obtain ⟨events, last, run, terminal⟩ := Result.run_reaches
      (call __TRY_REOPEN__ 3#u32) failedSyncBoot []
    exact ⟨events, last, _, run, terminal,
      captured_restart last (Concurrent.checkPost_sound checked run terminal)⟩
  · cbv

end Record.TornSyncRecovery
