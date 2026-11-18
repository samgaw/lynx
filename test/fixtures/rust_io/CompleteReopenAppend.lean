module
public import Record.CompleteNamedRepair
import Lynx.Runner.NativeArithmetic
public section
open Aeneas Aeneas.Std Lynx io_native
namespace Record.CompleteReopenAppend
open NativeFile
open Record.CompleteNamedRepair (completeBytes finishComplete exactState)
open Record.ReopenedLogProperties (names finalEnvironment)
open Record.ReopenedRepairPrefix (CrashAttempts registered script)
open Record.RepeatedRepairProperties (repairScript)
open Record.Properties (outcome)
open Record.RecoveryProperties (zeroMask)
open Record.CrashProperties (disk)
open Record.LogProperties (logBytes)
open scoped Lynx.NativeArithmetic

@[expose] def finalBytes (left committed : Bool) : ByteArray :=
  disk (logBytes ([13#u16, if left then 19#u16 else 23#u16] ++ if committed then [29#u16] else []))

@[expose] def appendScript (bytes : ByteArray) (commit : Bool) : Term :=
  let mask := zeroMask bytes
  let sync := outcome "sync_all" true 0 .empty .nil
  outcome "seek" true 0 mask
    (outcome "write" true (if commit then 4 else 2) mask
      (if commit then sync else outcome "set_len" true 0 mask sync))

@[expose] def resumeScript (bytes : ByteArray) (commit : Bool) : Term :=
  script (repairScript bytes (appendScript bytes commit))

@[expose] def bootState (counter : Nat) (bytes : ByteArray) (commit : Bool) : Environment := {
  nativeRefCounter := counter
  nativeHeap := [
    (0, namespaceTypeName, encodeNamespace ⟨names, names, [], resumeScript bytes commit⟩),
    (1, inodeTypeName, encode ⟨bytes, bytes, 0, .nil⟩)] }

@[expose] def reopenAppend
    (reopen : U32 → NativeM (NativeResourceArc shared_log.LogResource))
    (append : NativeResourceArc shared_log.LogResource → U16 → NativeM Bool) : Result Term := do
  let resource ← finishComplete reopen
  let owner ← NativeResourceArc.decode resource
  Rustler.executeNative (append owner 29#u16) Rustler.encodeBool

@[expose] def appendState (counter : Nat) (left committed : Bool) (last : Concurrent.Config Term) : Bool :=
  let env := finalEnvironment last
  match getHandle ⟨counter + 1⟩ writableHandleTypeName env with
  | some handle =>
    let payload : shared_log.LogResource := ⟨⟨counter + 2⟩⟩
    exactState counter (finalBytes left committed) last &&
    handle.inode == 1 && handle.position == (if committed then 12 else 10) && handle.script == .nil &&
    env.nativeRefCounter == counter + 8 &&
    (NativeResourceArc.vmCells payload (counter + 3) (counter + 5) (counter + 6)).all env.nativeHeap.contains &&
    !env.nativeHeap.any (fun cell => cell.1 == counter + 4 || counter + 7 ≤ cell.1) &&
    env.nativeHeap.contains (counter + 2, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference (counter + 1)])
  | none => false

@[expose] def appendFinal (counter : Nat) (left committed : Bool) (last : Concurrent.Config Term) : Bool :=
  match last.outcome with
  | .ok (.atom reply) =>
    reply == (if committed then "true" else "false") && appendState counter left committed last
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
private theorem append_checked (counter : Nat) (left committed : Bool) (positive : 1 ≤ counter)
    (elapsed : PID → Nat → Nat) :
    let bytes := completeBytes left
    restartFilesystem ⟨names, [(1, bytes)], counter⟩ (resumeScript bytes committed) =
      some (bootState counter bytes committed) ∧
    Concurrent.checkPost (appendFinal counter left committed) 128
      (.start (registered (bootState counter bytes committed)) (reopenAppend __REOPEN__ __APPEND__) elapsed) = true := by
  cases left <;> cases committed <;> constructor <;> cbv

/-- After any admitted series of crashes, reopening the same inode supplies a live
writable handle. An acknowledged append persists the third record, and a successful
rollback of a short write leaves the two original records. Both leave the same
named inode and original pin available for subsequent calls. -/
theorem append_after_repeated_reopen (left committed : Bool) (count : Nat) (before after : FilesystemImage)
    (positive : 1 ≤ before.highWater)
    (complete : before = ⟨names, [(1, completeBytes left)], before.highWater⟩)
    (attempts : CrashAttempts (fun _ => __REOPEN__ 3#u32) count before after) :
    ∃ boot, restartFilesystem after (resumeScript (completeBytes left) committed) = some boot ∧
      ∀ elapsed events last answer,
        Concurrent.Run (.start (registered boot) (reopenAppend __REOPEN__ __APPEND__) elapsed) events last →
        Concurrent.Terminal last answer → appendFinal after.highWater left committed last = true := by
  obtain ⟨advances, same, _⟩ := Record.CompleteNamedRepair.retry_complete_log left count before after positive complete attempts
  have fresh := Nat.le_trans positive advances
  refine ⟨bootState after.highWater (completeBytes left) committed, ?_, ?_⟩
  · rw [same]
    exact (append_checked after.highWater left committed fresh (fun _ _ => 0)).1
  · intro elapsed events last answer run terminal
    exact Concurrent.checkPost_sound (append_checked after.highWater left committed fresh elapsed).2 run terminal

@[expose] def commitBoot : Environment := registered (bootState 2 (completeBytes true) true)

@[expose] def rollbackBoot : Environment := registered (bootState 2 (completeBytes false) false)

/-- Both law environments follow an actual interrupted named reopen. Their only
extra host choices are the new writable descriptor's append or rollback. -/
theorem resume_boot_reachable (committed : Bool) :
    let bytes := completeBytes committed
    let after : FilesystemImage := ⟨names, [(1, bytes)], 2⟩
    CrashAttempts (fun _ => __REOPEN__ 3#u32) 1 ⟨names, [(1, bytes)], 1⟩ after ∧
    (restartFilesystem after (resumeScript bytes committed)).map registered =
      some (if committed then commitBoot else rollbackBoot) := by
  have interrupted := Record.CompleteNamedRepair.complete_attempts_witness 1 1 committed (by decide)
  refine ⟨interrupted, ?_⟩
  rw [(append_checked 2 committed committed (by decide) (fun _ _ => 0)).1]
  cases committed <;> rfl

@[expose] def appendLaw (committed : Bool) (last : Concurrent.Config Term) : Bool :=
  match last.outcome with
  | .ok (.atom "true") => appendState 2 committed committed last
  | _ => false

theorem append_law_outcome (committed : Bool) (last : Concurrent.Config Term)
    (accepted : appendLaw committed last = true) : last.outcome = .ok Term.true := by
  unfold appendLaw at accepted
  split at accepted
  · assumption
  · contradiction

end Record.CompleteReopenAppend
