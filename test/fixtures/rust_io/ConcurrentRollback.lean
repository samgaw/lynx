module
public import Record.ReopenedRepairPrefix
public import Record.EncodedPrefixRecovery
public import Lynx.Concurrent
public import Lynx.Modules.Erlang.erlang.Process
import Lynx.Runner.CheckPost
public section
open Aeneas Aeneas.Std Lynx io_native
namespace Record.ConcurrentRollback
open NativeFile Record.ReopenedLogProperties Record.ReopenedRepairPrefix
open Record.CrashProperties (disk)
open Record.Properties (outcome)
open Record.LogProperties (logBytes)
open Record.RecoveryProperties (zeroMask)

@[expose] def bytesFor (value : U16) : ByteArray := disk (logBytes [13#u16, value])

@[expose] def remainingIO : Term :=
  let mask := zeroMask (bytesFor 19#u16)
  afterRepair "seek" 0 (afterRepair "write" 4 (afterRepair "sync_all" 0
    (outcome "seek" true 0 mask (outcome "write" true 2 mask
      (outcome "set_len" true 0 mask (outcome "sync_all" true 0 .empty .nil))))))

@[expose] def initial : Environment := initialFor remainingIO

@[expose] def writeCall
    (append : NativeResourceArc shared_log.LogResource → U16 → NativeM Bool)
    (resource : Term) (value : U16) : Result Term := do
  let owner ← NativeResourceArc.decode resource
  Rustler.executeNative (append owner value) Rustler.encodeBool

@[expose] def bothWriters
    (append : NativeResourceArc shared_log.LogResource → U16 → NativeM Bool)
    (resource : Term) : Result Term := do
  let _ ← Result.schedule {} (do
    let reply ← writeCall append resource 23#u16
    Result.send [] (.tuple #[.atom "writer", reply]) (.ok Term.true)) .ok
  let left ← writeCall append resource 19#u16
  let _ ← Erlang.erlang.«put/2» (Dispatcher.ofTable [] 0) (.atom "left_ack") left
  let right ← Result.receive .infinity (fun _ term => match term with
    | .tuple fields => if fields[0]? == some (.atom "writer") then fields[1]? else none
    | _ => none) (fun reply => .ok (reply.getD Term.false))
  let _ ← Erlang.erlang.«put/2» (Dispatcher.ofTable [] 0) (.atom "right_ack") right
  Result.ok (.tuple #[left, right])

@[expose] def acknowledged (key : String) (env : Environment) : Bool :=
  env.pdict.any (fun entry => entry.1 == .atom key && entry.2 == Term.true)

@[expose] def hasPrefix (prefixBytes bytes : ByteArray) : Bool :=
  prefixBytes.size ≤ bytes.size &&
    (List.range prefixBytes.size).all (fun i => prefixBytes[i]! == bytes[i]!)

@[expose] def safeData (base bytes : ByteArray) : Bool := hasPrefix base bytes && bytes.size ≤ 10

@[expose] def holdsAcknowledged (env : Environment) (state : State) : Bool :=
  let left := bytesFor 19#u16
  let right := bytesFor 23#u16
  safeData repaired state.visible && safeData repaired state.durable &&
    (!acknowledged "left_ack" env ||
      (safeData left state.visible && safeData left state.durable)) &&
    (!acknowledged "right_ack" env ||
      (safeData right state.visible && safeData right state.durable))

@[expose] def retained (config : Concurrent.Config Term) : Bool :=
  let env := finalEnvironment config
  1 ≤ env.nativeRefCounter && inodeIds env == [1] &&
    (match namespaceSnapshot env with
    | some table => tablesEqual table.names names && tablesEqual table.committed names && table.pending.isEmpty
    | none => false) &&
    (match inode 1 env with
    | some state => holdsAcknowledged env state
    | none => false)

@[expose] def finalFor (value : U16) (env : Environment) : Bool :=
  match lookup ⟨2⟩ env with
  | some file =>
    file.visible.data == (bytesFor value).data && file.durable.data == (bytesFor value).data &&
    file.position == 10 && file.script == .nil && env.nativeRefCounter == 11 &&
    (NativeResourceArc.vmCells (⟨⟨3⟩⟩ : shared_log.LogResource) 4 6 7).all env.nativeHeap.contains &&
    env.nativeHeap.contains (3, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference 2]) &&
    !env.nativeHeap.any (fun cell => cell.1 == 5 || 8 ≤ cell.1)
  | none => false

@[expose] def afterReopen : Environment := {
  nativeRefCounter := 7
  nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource]
  pdict := [(.atom "log", .nativeReference 7)]
  nativeHeap := NativeResourceArc.vmCells (⟨⟨3⟩⟩ : shared_log.LogResource) 4 6 7 ++ [
    (3, NativeMutex.typeName NativeFile, .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference 2]),
    (2, writableHandleTypeName, encodeHandle ⟨1, 6, remainingIO⟩),
    (0, namespaceTypeName, encodeNamespace ⟨names, names, [], .nil⟩),
    (1, inodeTypeName, encode ⟨repaired, repaired, 0, .nil⟩)] }

@[expose] def reopenThenStore
    (reopen : U32 → NativeM (NativeResourceArc shared_log.LogResource)) : Result Term := do
  let resource ← finish reopen
  let _ ← Erlang.erlang.«put/2» (Dispatcher.ofTable [] 0) (.atom "log") resource
  Result.ok resource

@[expose] def reopenAndWrite
    (reopen : U32 → NativeM (NativeResourceArc shared_log.LogResource))
    (append : NativeResourceArc shared_log.LogResource → U16 → NativeM Bool) : Result Term :=
  reopenThenStore reopen >>= bothWriters append

private def startsScheduling : Concurrent.Config α → Bool
  | .start env computation _ => Concurrent.isRequest env computation
  | .running .. => false

private def checkReopen (accept : Concurrent.Config α → Bool) :
    Nat → Concurrent.Config α → Option (Concurrent.Config α)
  | 0, _ => none
  | depth + 1, config =>
    if accept config then
      if startsScheduling config then some config
      else match config.successors with
        | [(_, next)] => checkReopen accept depth next
        | _ => none
    else none

/-- A checked sequential prefix reaches its exact checkpoint. Every raw run
either ends at a checked prefix or continues from that checkpoint. -/
private theorem checkReopen_sound {first checkpoint : Concurrent.Config α} {depth : Nat}
    {accept : Concurrent.Config α → Bool}
    (checked : checkReopen accept depth first = some checkpoint) :
    ∃ events, Concurrent.Run first events checkpoint ∧
      ∀ {laterEvents last}, Concurrent.Run first laterEvents last →
        accept last = true ∨ ∃ remaining, Concurrent.Run checkpoint remaining last := by
  induction depth generalizing first with
  | zero => simp [checkReopen] at checked
  | succ depth ih =>
    unfold checkReopen at checked
    split at checked
    · rename_i intact
      split at checked
      · cases Option.some.inj checked
        exact ⟨[], .refl, fun run => .inr ⟨_, run⟩⟩
      · split at checked
        · rename_i event next single
          obtain ⟨events, reaches, covers⟩ := ih checked
          refine ⟨event :: events, .step (by simp [Concurrent.Step, single]) reaches, ?_⟩
          intro laterEvents last run
          cases run with
          | refl => exact .inl intact
          | step step rest =>
            simp [Concurrent.Step, single] at step
            obtain ⟨rfl, rfl⟩ := step
            exact covers rest
        · contradiction
    · contradiction

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
private theorem reopening_checked (elapsed : PID → Nat → Nat) :
    checkReopen retained 64 (.start initial (reopenAndWrite __REOPEN__ __APPEND__) elapsed) =
      some (.start afterReopen (bothWriters __APPEND__ (.nativeReference 7)) elapsed) := by
  set_option cbv.maxSteps 32000000 in cbv

theorem reopening_supplies_resource (elapsed : PID → Nat → Nat) :
    ∃ events, Concurrent.Run (.start initial (reopenAndWrite __REOPEN__ __APPEND__) elapsed)
      events (.start afterReopen (bothWriters __APPEND__ (.nativeReference 7)) elapsed) := by
  obtain ⟨events, run, _⟩ := checkReopen_sound (reopening_checked elapsed)
  exact ⟨events, run⟩


set_option maxHeartbeats 128000000 in
set_option maxRecDepth 8192 in
theorem prefixes_checked (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant retained 256
      (.start afterReopen (bothWriters __APPEND__ (.nativeReference 7)) elapsed) = true := by
  lynx_check_invariant

theorem all_prefixes_safe (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config Term}
    (run : Concurrent.Run (.start initial (reopenAndWrite __REOPEN__ __APPEND__) elapsed)
      events last) : retained last = true := by
  obtain ⟨_, _, covers⟩ := checkReopen_sound (reopening_checked elapsed)
  rcases covers run with preserved | ⟨_, afterReopening⟩
  · exact preserved
  · exact Concurrent.checkInvariant_sound (prefixes_checked elapsed) afterReopening

@[expose] def lawAccepted (config : Concurrent.Config Term) : Bool :=
  config.outcome.isTrue &&
    (finalFor 19#u16 (finalEnvironment config) || finalFor 23#u16 (finalEnvironment config))

theorem law_outcome (config : Concurrent.Config Term) (accepted : lawAccepted config = true) :
    config.outcome = .ok Term.true := by
  simp only [lawAccepted, Bool.and_eq_true] at accepted
  exact Outcome.eq_of_isTrue accepted.1

open io_native.io_protocol (recover_log)
open Record.RepairCrashProperties (Prefix LogImage persist_lengths)
open Record.EncodedPrefixRecovery (persist_prefix restart_prefix)
open Record.CrashProperties (recoveryScript scanning)
open Record.RecoveryProperties (restarted)
open Record.Properties (fileEnv)

@[expose] def records (winner : Option Bool) : List U16 :=
  match winner with
  | none => [13#u16]
  | some true => [13#u16, 19#u16]
  | some false => [13#u16, 23#u16]

@[expose] def observed (winner : Option Bool) (env : Environment) : Bool :=
  match winner with
  | none => true
  | some true => acknowledged "left_ack" env
  | some false => acknowledged "right_ack" env

private theorem data_prefix (base bytes : ByteArray) (safe : safeData base bytes = true) :
    Prefix base bytes ∧ bytes.size ≤ 10 := by
  simp only [safeData, hasPrefix, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, beq_iff_eq] at safe
  exact ⟨⟨safe.1.1, fun i inside => (safe.1.2 i (List.mem_range.mpr inside)).symm⟩, safe.2⟩

private theorem safe_images (winner : Option Bool) (env : Environment) (file : State)
    (kept : holdsAcknowledged env file = true) (known : observed winner env = true) :
    safeData (disk (logBytes (records winner))) file.visible = true ∧
    safeData (disk (logBytes (records winner))) file.durable = true := by
  simp only [holdsAcknowledged, Bool.and_eq_true] at kept
  obtain ⟨⟨⟨visible, durable⟩, left⟩, right⟩ := kept
  cases winner with
  | none =>
    have original : disk (logBytes (records none)) = repaired := by decide +kernel
    simpa only [original] using And.intro visible durable
  | some first =>
    cases first
    · change acknowledged "right_ack" env = true at known
      simpa only [known, Bool.not_true, Bool.false_or, Bool.and_eq_true, records, bytesFor] using right
    · change acknowledged "left_ack" env = true at known
      simpa only [known, Bool.not_true, Bool.false_or, Bool.and_eq_true, records, bytesFor] using left

private theorem kept_crash (config : Concurrent.Config Term) (intact : retained config = true)
    (winner : Option Bool) (observedWinner : observed winner (finalEnvironment config) = true)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (captured : filesystemCrashImage chosen masks (finalEnvironment config) = some image) :
    ∃ bytes, image = ⟨names, [(1, bytes)], (finalEnvironment config).nativeRefCounter⟩ ∧
      1 ≤ image.highWater ∧ Prefix (disk (logBytes (records winner))) bytes ∧ bytes.size ≤ 10 := by
  unfold retained at intact
  dsimp only at intact
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at intact
  obtain ⟨⟨⟨positive, ids⟩, table⟩, contents⟩ := intact
  split at table
  · rename_i snapshot tables
    simp only [Bool.and_eq_true, List.isEmpty_iff] at table
    obtain ⟨⟨visible, committed⟩, pending⟩ := table
    have fixed : namespaceSnapshot (finalEnvironment config) =
        some ⟨names, names, [], snapshot.script⟩ := by
      rw [tables]
      have same := names_equal _ _ visible
      have stable := names_equal _ _ committed
      cases snapshot
      simp_all
    split at contents
    · rename_i state found
      obtain ⟨mask, bytes, persisted, same⟩ :=
        captured_journal _ state snapshot.script fixed ids found chosen masks image captured
      obtain ⟨v, d⟩ := safe_images winner _ _ contents observedWinner
      have visible := data_prefix _ _ v
      have durable := data_prefix _ _ d
      have sizes := persist_lengths _ _ _ _ persisted
      exact ⟨bytes, same, by simpa [same] using positive,
        persist_prefix _ _ _ _ _ durable.1 visible.1 persisted, by omega⟩
    · contradiction
  · contradiction

private theorem record_count (winner : Option Bool) : (records winner).length ≤ 262144 := by
  cases winner with
  | none => decide
  | some first => cases first <;> decide

/-- After a crash at any reached prefix, the actual Rust reader recovers the
old record and any append observed as successful by the root process. Other
visible or persisted bytes need not belong to an acknowledged operation. -/
theorem recover_observed (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config Term}
    (run : Concurrent.Run (.start initial (reopenAndWrite __REOPEN__ __APPEND__) elapsed) events last)
    (winner : Option Bool) (known : observed winner (finalEnvironment last) = true)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (captured : filesystemCrashImage chosen masks (finalEnvironment last) = some image)
    (rest : Term) :
    ∃ bytes, image = ⟨names, [(1, bytes)], (finalEnvironment last).nativeRefCounter⟩ ∧
      let values := records winner
      let file := (⟨image.highWater + 1⟩ : NativeFile)
      recover_log file (Usize.ofNatCore values.length (by have := record_count winner; scalar_tac))
        (restarted ⟨bytes, image.highWater⟩ (recoveryScript bytes rest)) =
        (.ok (.Ok (alloc.vec.Vec.from values (by have := record_count winner; scalar_tac)), file),
          fileEnv ({} : Environment) file (scanning bytes rest (4 * values.length)) []) := by
  have invariant := all_prefixes_safe elapsed run
  obtain ⟨bytes, named, _, present, small⟩ := kept_crash last invariant winner known
    chosen masks image captured
  exact ⟨bytes, named, restart_prefix (records winner) ⟨bytes, image.highWater⟩ rest present
    (by dsimp; unfold limit; omega) (record_count winner)⟩

end Record.ConcurrentRollback
