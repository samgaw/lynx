module
public import Record.ReopenedRepairPrefix
import Lynx.Runner.NativeArithmetic
public section
open Aeneas Aeneas.Std Lynx io_native
namespace Record.CompleteNamedRepair
open NativeFile Record.ReopenedLogProperties Record.ReopenedRepairPrefix
open Record.CrashProperties (disk)
open Record.LogProperties (logBytes)
open scoped Lynx.NativeArithmetic

@[expose] def completeBytes (left : Bool) : ByteArray :=
  disk (logBytes [13#u16, if left then 19#u16 else 23#u16])

-- Two complete records need a third scan slot to observe EOF.
@[expose] def finishComplete
    (reopen : U32 → NativeM (NativeResourceArc shared_log.LogResource)) : Result Term :=
  finish (fun _ => reopen 3#u32)

@[expose] def exactState (counter : Nat) (bytes : ByteArray) (config : Concurrent.Config Term) : Bool :=
  let env := finalEnvironment config
  counter ≤ env.nativeRefCounter && inodeIds env == [1] &&
  (match namespaceSnapshot env with
   | some table =>
     tablesEqual table.names names && tablesEqual table.committed names && table.pending.isEmpty
   | none => false) &&
  (match inode 1 env with
   | some file => file.visible.data == bytes.data && file.durable.data == bytes.data
   | none => false)

@[expose] def liveResource (counter : Nat) (bytes : ByteArray) (pin : Nat)
    (env : Environment) : Bool :=
  match lookup ⟨counter + 1⟩ env with
  | some file =>
    let payload : shared_log.LogResource := ⟨⟨counter + 2⟩⟩
    pin == counter + 6 && env.nativeRefCounter == pin &&
    file.position == bytes.size && file.script == .nil &&
    (NativeResourceArc.vmCells payload (counter + 3) (counter + 5) pin).all env.nativeHeap.contains &&
    !env.nativeHeap.any (fun cell => cell.1 == counter + 4) &&
    env.nativeHeap.contains (counter + 2, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference (counter + 1)])
  | none => false

@[expose] def completeReturn (counter : Nat) (bytes : ByteArray)
    (config : Concurrent.Config Term) : Bool :=
  exactState counter bytes config &&
    (match config.outcome with
     | .ok (.nativeReference pin) => liveResource counter bytes pin (finalEnvironment config)
     | _ => false)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
private theorem checked_prefixes (counter : Nat) (left syncs : Bool) (positive : 1 ≤ counter)
    (elapsed : PID → Nat → Nat) :
    let bytes := completeBytes left
    restartFilesystem ⟨names, [(1, bytes)], counter⟩ (reopenScript bytes syncs) = some (cold counter bytes syncs) ∧
    Concurrent.checkInvariant (exactState counter bytes) 64
      (.start (registered (cold counter bytes syncs)) (finishComplete __REOPEN__) elapsed) = true := by
  cases left <;> cases syncs <;> constructor <;> cbv

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
private theorem checked_complete (counter : Nat) (left : Bool) (positive : 1 ≤ counter)
    (elapsed : PID → Nat → Nat) :
    let bytes := completeBytes left
    Concurrent.checkPost (completeReturn counter bytes) 64
      (.start (registered (cold counter bytes true)) (finishComplete __REOPEN__) elapsed) = true := by
  cases left <;> cbv

/-- A crash of the synchronized named journal retains both the namespace and exact bytes. -/
theorem capture_exact (counter : Nat) (bytes : ByteArray) (config : Concurrent.Config Term)
    (safe : exactState counter bytes config = true) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (finalEnvironment config) = some image) :
    image = ⟨names, [(1, bytes)], image.highWater⟩ ∧ counter ≤ image.highWater := by
  unfold exactState at safe
  dsimp only at safe
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at safe
  obtain ⟨⟨⟨advance, ids⟩, table⟩, contents⟩ := safe
  split at table
  · rename_i snapshot tables
    simp only [Bool.and_eq_true, List.isEmpty_iff] at table
    obtain ⟨⟨visible, committed⟩, pending⟩ := table
    have named : namespaceSnapshot (finalEnvironment config) =
        some ⟨names, names, [], snapshot.script⟩ := by
      rw [tables]
      have live := names_equal _ _ visible
      have durable := names_equal _ _ committed
      cases snapshot
      simp_all
    split at contents
    · rename_i file lookup
      simp only [Bool.and_eq_true, beq_iff_eq] at contents
      obtain ⟨mask, kept, accepted, captured⟩ :=
        captured_journal _ file snapshot.script named ids lookup chosen masks image crash
      rw [ByteArray.ext contents.1, ByteArray.ext contents.2] at accepted
      have stable := persist_same _ _ _ accepted
      subst kept
      exact ⟨by simp only [captured], by simpa only [captured] using advance⟩
    · contradiction
  · contradiction

private theorem preserve_attempt (left : Bool) (before after : FilesystemImage)
    (positive : 1 ≤ before.highWater)
    (complete : before = ⟨names, [(1, completeBytes left)], before.highWater⟩)
    (attempt : CrashAttempt (fun _ => __REOPEN__ 3#u32) before after) :
    after = ⟨names, [(1, completeBytes left)], after.highWater⟩ ∧ before.highWater ≤ after.highWater := by
  obtain ⟨bytes, syncs, boot, elapsed, events, last, chosen, masks, given, ready, run, crash⟩ := attempt
  have same : bytes = completeBytes left := by
    simpa using congrArg FilesystemImage.inodes (given.symm.trans complete)
  subst bytes
  have checked := checked_prefixes before.highWater left syncs positive elapsed
  rw [complete] at ready
  have sameBoot := Option.some.inj (ready.symm.trans checked.1)
  subst boot
  exact capture_exact _ _ last (Concurrent.checkInvariant_sound checked.2 run) chosen masks after crash

/-- Any finite number of admitted crashes during actual named reopens keeps
both records and the original named inode. Reboot discards the old handles.
On a successful host script the actual NIF returns a fresh pinned resource. -/
theorem retry_complete_log (left : Bool) (count : Nat) (before after : FilesystemImage)
    (positive : 1 ≤ before.highWater)
    (complete : before = ⟨names, [(1, completeBytes left)], before.highWater⟩)
    (attempts : CrashAttempts (fun _ => __REOPEN__ 3#u32) count before after) :
    let bytes := completeBytes left
    before.highWater ≤ after.highWater ∧
    after = ⟨names, [(1, bytes)], after.highWater⟩ ∧
    ∃ boot, restartFilesystem after (reopenScript bytes true) = some boot ∧
      ∀ elapsed events last outcome,
        Concurrent.Run (.start (registered boot) (finishComplete __REOPEN__) elapsed) events last →
        Concurrent.Terminal last outcome → completeReturn after.highWater bytes last = true := by
  have kept : after = ⟨names, [(1, completeBytes left)], after.highWater⟩ ∧
      before.highWater ≤ after.highWater := by
    induction attempts with
    | zero => exact ⟨complete, Nat.le_refl _⟩
    | next head _ ih =>
      obtain ⟨same, advances⟩ := preserve_attempt left _ _ positive complete head
      obtain ⟨final, monotone⟩ := ih (Nat.le_trans positive advances) same
      exact ⟨final, Nat.le_trans advances monotone⟩
  have high := Nat.le_trans positive kept.2
  refine ⟨kept.2, kept.1, cold after.highWater (completeBytes left) true, ?_, ?_⟩
  · rw [kept.1]
    exact (checked_prefixes after.highWater left true high (fun _ _ => 0)).1
  · intro elapsed events last outcome run terminal
    exact Concurrent.checkPost_sound (checked_complete after.highWater left high elapsed) run terminal

private def captureBlocked (bytes : ByteArray) (last : Concurrent.Config Term) : Option FilesystemImage :=
  filesystemCrashImage names [(1, Record.RecoveryProperties.zeroMask bytes)] (finalEnvironment last)

private def blockedWith (counter : Nat) (bytes : ByteArray) (last : Concurrent.Config Term) : Bool :=
  match last.outcome, captureBlocked bytes last with
  | .deadlock, some ⟨chosen, [(1, saved)], high⟩ =>
    tablesEqual chosen names && saved.data == bytes.data && high == counter + 1
  | _, _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
private theorem blocked_checked (counter : Nat) (left : Bool) (positive : 1 ≤ counter) :
    let bytes := completeBytes left
    Concurrent.checkPost (blockedWith counter bytes) 64
      (.start (registered (cold counter bytes false)) (finishComplete __REOPEN__)) = true := by
  cases left <;> cbv

/-- The named reboot can reach a real blocked sync under the declared host
script. Capturing the unchanged disk there advances descriptor freshness. -/
theorem blocked_complete (counter : Nat) (left : Bool) (positive : 1 ≤ counter) :
    CrashAttempt (fun _ => __REOPEN__ 3#u32)
      ⟨names, [(1, completeBytes left)], counter⟩ ⟨names, [(1, completeBytes left)], counter + 1⟩ := by
  let bytes := completeBytes left
  let boot := cold counter bytes false
  obtain ⟨events, last, run, terminal⟩ := Result.run_reaches (finishComplete __REOPEN__) (registered boot) []
  have accepted := Concurrent.checkPost_sound (blocked_checked counter left positive) run terminal
  have saved : captureBlocked bytes last = some ⟨names, [(1, bytes)], counter + 1⟩ := by
    unfold blockedWith at accepted
    split at accepted
    · rename_i chosen persisted high outcome captured
      simp only [Bool.and_eq_true, beq_iff_eq] at accepted
      obtain ⟨⟨table, exactBytes⟩, watermark⟩ := accepted
      rw [captured, names_equal _ _ table, ByteArray.ext exactBytes, watermark]
    · contradiction
  exact ⟨bytes, false, boot, _, events, last, names, [(1, Record.RecoveryProperties.zeroMask bytes)], rfl,
    (checked_prefixes counter left false positive (fun _ _ => 0)).1, run, saved⟩

/-- For each interruption count there is a named trace that blocks on sync
and crashes at every reboot, retaining bytes and monotone handle identities. -/
theorem complete_attempts_witness (counter count : Nat) (left : Bool) (positive : 1 ≤ counter) :
    CrashAttempts (fun _ => __REOPEN__ 3#u32) count
      ⟨names, [(1, completeBytes left)], counter⟩
      ⟨names, [(1, completeBytes left)], counter + count⟩ := by
  induction count generalizing counter with
  | zero => exact .zero
  | succ count ih =>
    have chain := CrashAttempts.next (blocked_complete counter left positive)
      (ih (counter + 1) (by omega))
    simpa only [Nat.add_right_comm counter 1 count, Nat.add_assoc] using chain

@[expose] def completeBoot : Environment := registered (cold 2 (completeBytes true) true)

/-- The complete-log law starts from an image reached by an actual blocked
reopen, followed by successful rehydration of that named image. -/
theorem complete_boot_reachable :
    let bytes := completeBytes true
    let captured : FilesystemImage := ⟨names, [(1, bytes)], 2⟩
    CrashAttempt (fun _ => __REOPEN__ 3#u32) ⟨names, [(1, bytes)], 1⟩ captured ∧
    (restartFilesystem captured (reopenScript bytes true)).map registered = some completeBoot := by
  refine ⟨blocked_complete 1 true (by decide), ?_⟩
  rw [(checked_prefixes 2 true true (by decide) (fun _ _ => 0)).1]
  rfl

@[expose] def completeLaw (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.atom "true") =>
    exactState 2 (completeBytes true) config && liveResource 2 (completeBytes true) 8 (finalEnvironment config)
  | _ => false

theorem complete_law_outcome (config : Concurrent.Config Term)
    (accepted : completeLaw config = true) : config.outcome = .ok Term.true := by
  unfold completeLaw at accepted
  split at accepted
  · assumption
  · contradiction

end Record.CompleteNamedRepair
