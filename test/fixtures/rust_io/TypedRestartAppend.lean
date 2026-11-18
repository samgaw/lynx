module
public import Record.TornSyncChains
import Lynx.Runner.NativeArithmetic

public section

open Aeneas Aeneas.Std Lynx io_native

namespace Record.TypedRestartAppend
open NativeFile
open scoped Lynx.NativeArithmetic
open Record.FallibleReopen (journalName contents call environment)
open Record.NamedJournalCrash (inodeIds names_equal captured_journal)
open Record.TornSyncFailure (withTail choose zeros tail_forms)
open Record.TornSyncChains (Reopen JournalImage FailedAttempts repeated_failed_sync)
open Record.TornSyncRecovery (names registered image_shape cold restartImage)
open Record.TornSyncChains (failed_attempt_witness)

@[expose] def appendScript (committed : Bool) : Term :=
  let mask := zeros 8
  let sync := choose "sync_all" true 0 ByteArray.empty .nil
  choose "seek" true 0 mask
    (choose "write" true (if committed then 4 else 2) mask
      (if committed then sync else choose "set_len" true 0 mask sync))

@[expose] def boot (counter : Nat) (data : ByteArray) (committed : Bool) : Environment :=
  cold counter data (appendScript committed)

@[expose] def reopenAppend (reopen : Reopen)
    (append : NativeResourceArc shared_log.LogResource → U16 → NativeM Bool) : Result Term := do
  let pin ← call reopen 3#u32
  let owner ← NativeResourceArc.decode pin
  Rustler.executeNative (append owner 29#u16) Rustler.encodeBool

@[expose] def finalBytes (left committed : Bool) : ByteArray :=
  if committed then withTail left [29,0,226,255] else contents left

@[expose] def appendState (counter : Nat) (left committed : Bool) (env : Environment) : Bool :=
  match inode 1 env, namespaceSnapshot env,
      getHandle ⟨counter + 1⟩ writableHandleTypeName env with
  | some file, some table, some handle =>
    let payload : shared_log.LogResource := ⟨⟨counter + 2⟩⟩
    file.visible.data == (finalBytes left committed).data && file.durable.data == (finalBytes left committed).data &&
    tablesEqual table.names names && tablesEqual table.committed names &&
    table.pending.isEmpty && table.script == .nil && inodeIds env == [1] &&
    handle.inode == 1 && handle.position == (if committed then 12 else 10) && handle.script == .nil &&
    env.nativeRefCounter == counter + 8 &&
    (NativeResourceArc.vmCells payload (counter + 3) (counter + 5) (counter + 6)).all env.nativeHeap.contains &&
    !env.nativeHeap.any (fun cell => cell.1 == counter + 4 || counter + 7 ≤ cell.1) &&
    env.nativeHeap.contains (counter + 2, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference (counter + 1)])
  | _, _, _ => false

@[expose] def accepted (counter : Nat) (left committed : Bool) (last : Concurrent.Config Term) : Bool :=
  match last.outcome with
  | .ok (.atom reply) =>
    reply == (if committed then "true" else "false") &&
    appendState counter left committed (environment last)
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 64000000 in
theorem typed_reopen_append (counter : Nat) (left committed : Bool) (tail : List UInt8)
    (positive : 1 ≤ counter) (short : tail.length < 4) (elapsed : PID → Nat → Nat) :
    let data := withTail left tail
    restartFilesystem ⟨names, [(1, data)], counter⟩ (Record.TornSyncRecovery.script data (appendScript committed)) = some (boot counter data committed) ∧
    Concurrent.checkPost (accepted counter left committed) 128
      (.start (registered (boot counter data committed)) (reopenAppend __TRY_REOPEN__ __APPEND__) elapsed) = true := by
  rcases tail_forms tail short with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    cases left <;> cases committed <;> constructor <;> cbv

private theorem capture_after_append (counter : Nat) (left committed : Bool)
    (last : Concurrent.Config Term) (safe : accepted counter left committed last = true)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (environment last) = some image) :
    image = ⟨names, [(1, finalBytes left committed)], counter + 8⟩ := by
  unfold accepted at safe
  split at safe
  · simp only [Bool.and_eq_true] at safe
    have state := safe.2
    unfold appendState at state
    split at state
    · rename_i file table handle found snapshot opened
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at state
      have visible : file.visible = finalBytes left committed := ByteArray.ext (by tauto)
      have durable : file.durable = finalBytes left committed := ByteArray.ext (by tauto)
      have named : namespaceSnapshot (environment last) = some ⟨names, names, [], table.script⟩ := by
        rw [snapshot]
        have live : table.names = names := names_equal _ _ (by tauto)
        have stable : table.committed = names := names_equal _ _ (by tauto)
        have pending : table.pending = [] := by tauto
        cases table
        simp_all
      have ids : inodeIds (environment last) = [1] := by tauto
      have high : (environment last).nativeRefCounter = counter + 8 := by tauto
      obtain ⟨mask, bytes, accepted, captured⟩ :=
        captured_journal journalName _ file _ named ids found chosen masks image crash
      rw [visible, durable] at accepted
      rw [captured, NativeFile.persist_same _ _ _ accepted, high]
      rfl
    · contradiction
  · contradiction

/-- A captured crash after the actual typed recovery and append contains
exactly the synchronized third record or the prior acknowledged two records
after rollback. The short input tail cannot survive the successful repair. -/
theorem crash_after_typed_append (counter : Nat) (left committed : Bool) (tail : List UInt8)
    (positive : 1 ≤ counter) (short : tail.length < 4) (elapsed : PID → Nat → Nat)
    (events : List Concurrent.Event) (last : Concurrent.Config Term) (outcome : Outcome Term)
    (run : Concurrent.Run
      (.start (registered (boot counter (withTail left tail) committed))
        (reopenAppend __TRY_REOPEN__ __APPEND__) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (environment last) = some image) :
    image = ⟨names, [(1, finalBytes left committed)], counter + 8⟩ := by
  exact capture_after_append counter left committed last
    (Concurrent.checkPost_sound (typed_reopen_append counter left committed tail positive short elapsed).2
      run terminal) chosen masks image crash


/-- Continuing a journal after any finite series of typed failures and
crashes preserves the selected append or rollback across another crash. -/
theorem crash_after_repeated_failed_sync (left committed : Bool) (count : Nat)
    (before repaired : FilesystemImage) (safe : JournalImage left before)
    (attempts : FailedAttempts __TRY_REOPEN__ left count before repaired) :
    ∃ bytes restarted,
      restartFilesystem repaired (Record.TornSyncRecovery.script bytes (appendScript committed)) = some restarted ∧
      ∀ elapsed events last outcome,
        Concurrent.Run (.start (registered restarted) (reopenAppend __TRY_REOPEN__ __APPEND__) elapsed)
          events last → Concurrent.Terminal last outcome →
        ∀ chosen masks image,
          filesystemCrashImage chosen masks (environment last) = some image →
          image = ⟨names, [(1, finalBytes left committed)], repaired.highWater + 8⟩ := by
  obtain ⟨⟨data, previous, shape, positive⟩, _⟩ := repeated_failed_sync left count before repaired safe attempts
  obtain ⟨tail, short, rfl⟩ := image_shape left data shape
  refine ⟨withTail left tail, boot repaired.highWater (withTail left tail) committed, ?_, ?_⟩
  · have restarted := (typed_reopen_append repaired.highWater left committed tail positive short (fun _ _ => 0)).1
    rw [← previous] at restarted
    exact restarted
  · intro elapsed events last outcome run terminal chosen masks image crash
    exact crash_after_typed_append repaired.highWater left committed tail positive short elapsed
      events last outcome run terminal chosen masks image crash

@[expose] def resumed (committed : Bool) : Environment :=
  registered (boot 3 (withTail true [99]) committed)

@[expose] def commitBoot : Environment := resumed true
@[expose] def rollbackBoot : Environment := resumed false

set_option maxRecDepth 8192 in
/-- Both law environments follow a real failed-sync run and an admitted crash.
The host gives the new descriptor either a complete write or a short write. -/
theorem boot_after_failed_sync (committed : Bool) :
    FailedAttempts __TRY_REOPEN__ true 1
      ⟨names, [(1, withTail true [99,0])], 1⟩ restartImage ∧
    (restartFilesystem restartImage
      (Record.TornSyncRecovery.script (withTail true [99]) (appendScript committed))).map registered =
      some (resumed committed) := by
  exact ⟨failed_attempt_witness, by cbv⟩

@[expose] def lawAccepted (committed : Bool) (last : Concurrent.Config Term) : Bool :=
  match last.outcome with
  | .ok (.atom "true") => appendState 3 true committed (environment last)
  | _ => false

theorem law_outcome (committed : Bool) (last : Concurrent.Config Term)
    (checked : lawAccepted committed last = true) : last.outcome = .ok Term.true := by
  unfold lawAccepted at checked
  split at checked
  · assumption
  · contradiction

end Record.TypedRestartAppend
