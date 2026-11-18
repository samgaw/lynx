module
public import Record.Extraction.Funs
public import Record.SharedRecoveryProperties
public import Record.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx io_native
namespace Record.ReopenedLogProperties
open NativeFile Record.CrashProperties
attribute [local cbv_eval] Record.OverlappingLogProperties.caller_contract
  Record.RollbackProperties.append_contract
@[expose] def fileName : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩
@[expose] def names : Names := [(fileName,1)]
@[expose] def torn : ByteArray := ⟨#[13,0,242,255,99,0]⟩
@[expose] def repaired : ByteArray := ⟨#[13,0,242,255]⟩
@[expose] def zeros6 : ByteArray := ⟨#[0,0,0,0,0,0]⟩
@[expose] def action (operation : String) (count : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation,.atom "ok",.integer count,.bitstring zeros6 0]) rest
@[expose] def fileScript (rest : Term := .nil) : Term := action "seek" 0
  (action "read" 1 (action "read" 1 (action "read" 1 (action "read" 1
    (action "read" 1 (action "read" 1 (action "read" 0
      (action "set_len" 0 (action "sync_all" 0 rest)))))))))
@[expose] def initialFor (rest : Term) : Environment := {
  nativeRefCounter := 1
  nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource]
  nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨names,names,[],
      .cons (.tuple #[.atom "open",.bitstring fileName 0,.atom "ok",.integer 0,fileScript rest]) .nil⟩),
    (1,inodeTypeName,encode ⟨torn,torn,0,.nil⟩)] }
@[expose] def initial : Environment := initialFor .nil
@[expose] def finalEnvironment {α : Type} : Concurrent.Config α → Environment
  | .start env _ _ => env
  | .running state .. => state.nativeView []

@[expose] def repairedState (env : Environment) : Bool :=
  match lookup ⟨2⟩ env with
  | some file =>
    let payload : shared_log.LogResource := ⟨⟨3⟩⟩
    file.visible.data == repaired.data && file.durable.data == repaired.data &&
    file.position == 6 && env.nativeRefCounter == 7 &&
    (NativeResourceArc.vmCells payload 4 6 7).all (fun cell => env.nativeHeap.contains cell) &&
    !env.nativeHeap.any (fun cell => cell.1 == 5) &&
    env.nativeHeap.contains (3, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference 2])
  | none => false

@[expose] def accepted (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.nativeReference 7) => repairedState (finalEnvironment config)
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The actual Rust NIF repairs the tail, synchronizes and returns a pinned resource. -/
theorem reopened_checked : Concurrent.checkPost accepted 512
    (.start initial (do
      let owner ← __REOPEN__ 2#u32
      let term ← NativeResourceArc.encode owner
      NativeOwnedDrop.drop owner
      Result.ok term)) = true := by
  set_option cbv.maxSteps 32000000 in cbv
@[expose] def zeros4 : ByteArray := ⟨#[0,0,0,0]⟩
@[expose] def appended : ByteArray := ⟨#[13,0,242,255,19,0,236,255]⟩
@[expose] def afterRepair (operation : String) (count : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation,.atom "ok",.integer count,.bitstring zeros4 0]) rest
@[expose] def appendScript : Term := afterRepair "seek" 0
  (afterRepair "write" 4 (afterRepair "sync_all" 0 .nil))
@[expose] def shortScript : Term := afterRepair "seek" 0
  (afterRepair "write" 2 (afterRepair "set_len" 0 (afterRepair "sync_all" 0 .nil)))
@[expose] def appendInitial : Environment := initialFor appendScript
@[expose] def shortInitial : Environment := initialFor shortScript

/-- Both outcomes preserve the shared allocation, VM pin, open descriptor and
unlocked mutex. Acknowledgement requires the new durable record; successful
rollback must retain exactly the repaired prefix. -/
@[expose] def appendState (success : Bool) (env : Environment) : Bool :=
  match lookup ⟨2⟩ env, namespaceSnapshot env with
  | some file, some snapshot =>
    let payload : shared_log.LogResource := ⟨⟨3⟩⟩
    let expected := if success then appended else repaired
    file.visible.data == expected.data && file.durable.data == expected.data &&
    file.position == (if success then 8 else 6) && env.nativeRefCounter == 9 &&
    (NativeResourceArc.vmCells payload 4 6 7).all (fun cell => env.nativeHeap.contains cell) &&
    !env.nativeHeap.any (fun cell => cell.1 == 5 || cell.1 == 8) &&
    env.nativeHeap.contains (3,NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked",.atom "unpoisoned",.nativeReference 2]) &&
    namedInode snapshot.names fileName == some 1 &&
    namedInode snapshot.committed fileName == some 1
  | _, _ => false

@[expose] def appendAccepted (success : Bool) (config : Concurrent.Config Bool) : Bool :=
  match config.outcome with
  | .ok returned => returned == success && appendState success (finalEnvironment config)
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- Decode the returned VM resource and execute the actual Rust append caller. -/
theorem append_checked : Concurrent.checkPost (appendAccepted true) 768
    (.start appendInitial (do
      let owner ← __REOPEN__ 2#u32
      let term ← NativeResourceArc.encode owner
      NativeOwnedDrop.drop owner
      let decoded ← NativeResourceArc.decode term
      __APPEND__ decoded 19#u16)) = true := by
  set_option cbv.maxSteps 32000000 in cbv

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- A short write rolls back and synchronizes without losing the repaired resource. -/
theorem short_checked : Concurrent.checkPost (appendAccepted false) 768
    (.start shortInitial (do
      let owner ← __REOPEN__ 2#u32
      let term ← NativeResourceArc.encode owner
      NativeOwnedDrop.drop owner
      let decoded ← NativeResourceArc.decode term
      __APPEND__ decoded 19#u16)) = true := by
  set_option cbv.maxSteps 32000000 in cbv

/-- Records that must survive a crash after the admitted append outcome. -/
@[expose] def survivingRecords (success : Bool) : List U16 :=
  if success then [13#u16, 19#u16] else [13#u16]

private theorem surviving_bound (success : Bool) :
    (survivingRecords success).length ≤ 262144 := by
  cases success <;> decide

private theorem surviving_image (success : Bool) :
    (if success then appended else repaired) =
      disk (Record.LogProperties.logBytes (survivingRecords success)) := by
  cases success <;> decide +kernel

/-- For every admitted crash mask, the actual recovery loop reads exactly the
acknowledged records after the repaired resource's append or rollback. -/
theorem append_then_recover (success : Bool) {last : Concurrent.Config Bool}
    {events : List Concurrent.Event} {outcome : Outcome Bool}
    (run : Concurrent.Run
      (.start (if success then appendInitial else shortInitial) (do
        let owner ← __REOPEN__ 2#u32
        let term ← NativeResourceArc.encode owner
        NativeOwnedDrop.drop owner
        let decoded ← NativeResourceArc.decode term
        __APPEND__ decoded 19#u16)) events last)
    (terminal : Concurrent.Terminal last outcome)
    (mask : ByteArray) (image : Image) (rest : Term)
    (captured : crashImage ⟨2⟩ mask (finalEnvironment last) = some image) :
    let values := survivingRecords success
    io_native.io_protocol.recover_log ⟨image.highWater + 1⟩
      (Usize.ofNatCore values.length (by have := surviving_bound success; scalar_tac))
      (Record.RecoveryProperties.restarted image (recoveryScript image.bytes rest)) =
      (.ok (.Ok (alloc.vec.Vec.from values (by have := surviving_bound success; scalar_tac)),
        ⟨image.highWater + 1⟩),
        Record.Properties.fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          (scanning image.bytes rest (4 * values.length)) []) := by
  have checked : Concurrent.checkPost (appendAccepted success) 768
    (.start (if success then appendInitial else shortInitial) (do
      let owner ← __REOPEN__ 2#u32
      let term ← NativeResourceArc.encode owner
      NativeOwnedDrop.drop owner
      let decoded ← NativeResourceArc.decode term
      __APPEND__ decoded 19#u16)) = true := by
    cases success
    · exact short_checked
    · exact append_checked
  have accepted := Concurrent.checkPost_sound checked run terminal
  have state : appendState success (finalEnvironment last) = true := by
    unfold appendAccepted at accepted
    split at accepted
    · simp only [Bool.and_eq_true] at accepted
      exact accepted.2
    · contradiction
  unfold appendState at state
  split at state
  · rename_i file snapshot found named
    simp only [Bool.and_eq_true] at state
    let expected := if success then appended else repaired
    have visible : file.visible.data = expected.data := by
      simp only [beq_iff_eq] at state
      tauto
    have durable : file.durable.data = expected.data := by
      simp only [beq_iff_eq] at state
      tauto
    have visibleBytes := ByteArray.ext visible
    have durableBytes := ByteArray.ext durable
    exact Record.SharedRecoveryProperties.recover_shared_log ⟨2⟩ _ file
      (survivingRecords success) mask image rest found (durableBytes.trans visibleBytes.symm)
      (visibleBytes.trans (surviving_image success)) (surviving_bound success) captured
  · contradiction

/-- The ordinary Elixir law must acknowledge the result and preserve the native
state established by its implementation-linked properties. -/
@[expose] def appendedLawAccepted (success : Bool) (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.atom "true") => appendState success (finalEnvironment config)
  | _ => false

theorem appended_law_outcome (config : Concurrent.Config Term)
    (accepted : appendedLawAccepted success config = true) : config.outcome = .ok Term.true := by
  unfold appendedLawAccepted at accepted
  split at accepted
  · assumption
  · contradiction

@[expose] def lawAccepted (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.atom "true") => repairedState (finalEnvironment config)
  | _ => false

theorem accepted_outcome (config : Concurrent.Config Term)
    (accepted : lawAccepted config = true) : config.outcome = .ok Term.true := by
  unfold lawAccepted at accepted
  split at accepted
  · assumption
  · contradiction

end Record.ReopenedLogProperties
