module
public import Record.RepairWriterProperties
public import Record.RepeatedRepairProperties
public import Record.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.RepairingLogProperties
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties
  Record.RecoveryProperties Record.RepeatedRepairProperties

/-- The actual export consumes the decoded owner on success, limit and I/O error.
An error remains a false result, not a durable acknowledgement. -/
@[cbv_eval] theorem facade_contract (resource : NativeResourceArc shared_log.LogResource)
    (maximum : U32) (value : U16) :
    __REPAIR_APPEND__ resource maximum value = (do
      let converted ← NativeM.lift (UScalar.cast .Usize maximum)
      let reply ← shared_log.repair_append resource converted value
      NativeOwnedDrop.drop resource
      match reply with
      | .Ok accepted => NativeM.ok accepted
      | .Err error => do NativeOwnedDrop.drop error; NativeM.ok false) := by
  unfold __REPAIR_APPEND__
  rfl

/-- Resource dereference supplies the actual shared mutex identity to the
cross-crate repair/append body. No first-party contract is assumed. -/
@[cbv_eval] theorem critical_contract (resource : NativeResourceArc shared_log.LogResource)
    (maximum : Usize) (value : U16) :
    shared_log.repair_append resource maximum value = (do
      let log ← NativeResourceArc.deref resource
      locked_repair_and_append log.file maximum value) := by
  rfl

@[expose] def original : ByteArray := disk (logBytes [13#u16])
@[expose] def torn : ByteArray := disk (logBytes [13#u16] ++ [7#u8])
@[expose] def firstImage : ByteArray := disk (logBytes [13#u16,19#u16])
@[expose] def complete : ByteArray := disk (logBytes [13#u16,19#u16,23#u16])
@[expose] def appendScript (data : ByteArray) (rest : Term) : Term :=
  outcome "seek" true 0 (zeroMask data)
    (outcome "write" true 4 (zeroMask data)
      (outcome "sync_all" true 0 ByteArray.empty rest))
@[expose] def fileScript : Term := repairScript torn
  (appendScript original (repairScript firstImage (appendScript firstImage .nil)))
@[expose] def payload : shared_log.LogResource := ⟨⟨1⟩⟩
@[expose] def free : Term :=
  .tuple #[.atom "unlocked",.atom "unpoisoned",.nativeReference 2]
@[expose] def initialFor (script : Term) : Environment :=
  fileEnv ({
    nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource]
    pdict := [(.atom "log",.nativeReference 6)]
    nativeRefCounter := 6 } : Environment)
    ⟨2⟩ ⟨torn,torn,0,script⟩
    (NativeResourceArc.vmCells payload 3 5 6 ++ [(1,NativeMutex.typeName NativeFile,free)])
@[expose] def initial : Environment := initialFor fileScript
@[expose] def snapshot : Concurrent.Config α → Environment
  | .start env .. => env
  | .running state .. => state.nativeView []
@[expose] def stateAccepted (expected : ByteArray) (counter : Nat) (env : Environment) : Bool :=
  match lookup ⟨2⟩ env with
  | some file => file.visible == expected && file.durable == expected &&
      env.nativeRefCounter == counter &&
      (NativeResourceArc.vmCells payload 3 5 6).all (fun cell => env.nativeHeap.contains cell) &&
      env.nativeHeap.contains (1,NativeMutex.typeName NativeFile,free) &&
      !env.nativeHeap.any (fun cell => cell.1 == 4 || cell.1 == 7 || cell.1 == 8 || cell.1 == 9 || cell.1 == 10)
  | none => false
@[expose] def accepted (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.atom "true") => stateAccepted complete 10 (snapshot config)
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The compiled facade is called twice through the actual resource decoder and
result encoder. Both owners are consumed and the VM pin remains live. -/
theorem completed_checked : Concurrent.checkPost accepted 768
    (.start initial (do
      let first ← NativeResourceArc.decode (.nativeReference 6)
      let left ← Rustler.executeNative (__REPAIR_APPEND__ first 4#u32 19#u16) Rustler.encodeBool
      let second ← NativeResourceArc.decode (.nativeReference 6)
      let right ← Rustler.executeNative (__REPAIR_APPEND__ second 4#u32 23#u16) Rustler.encodeBool
      Result.ok (if left == Term.true && right == Term.true then Term.true else Term.false))) = true := by
  set_option cbv.maxSteps 32000000 in cbv

@[expose] def limitInitial : Environment := initialFor (outcome "seek" true 0 (zeroMask torn) .nil)
/-- Callback-free OS error destruction is an explicit external capability.
A missing/custom error must exhaust verification rather than disappear. -/
@[expose] def errorInitial : Environment :=
  let env := initialFor (outcome "seek" false 4 (zeroMask torn) .nil)
  {env with nativeHeap := (4,NativeIoError.typeName,.atom "live") :: env.nativeHeap}
@[expose] def rejected (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.atom "false") => stateAccepted torn 8 (snapshot config)
  | _ => false
@[expose] def unchangedAccepted (counter : Nat) (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.atom "true") => stateAccepted torn counter (snapshot config)
  | _ => false

set_option maxRecDepth 8192 in
/-- A recovery limit is false, preserves both images and releases the decoded
owner and mutex, rather than acknowledging an unexamined suffix. -/
theorem limit_checked : Concurrent.checkPost rejected 256
    (.start limitInitial (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__REPAIR_APPEND__ owner 0#u32 19#u16) Rustler.encodeBool)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- A real I/O error follows the extracted error/drop branch and does not
acknowledge, leak the decoded owner or leave the file mutex held. -/
theorem io_error_checked : Concurrent.checkPost rejected 256
    (.start errorInitial (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__REPAIR_APPEND__ owner 4#u32 19#u16) Rustler.encodeBool)) = true := by
  cbv

theorem unchanged_outcome (counter : Nat) (config : Concurrent.Config Term)
    (checked : unchangedAccepted counter config = true) : config.outcome = .ok Term.true := by
  unfold unchangedAccepted at checked
  split at checked
  · assumption
  · contradiction

theorem accepted_outcome (config : Concurrent.Config Term)
    (checked : accepted config = true) : config.outcome = .ok Term.true := by
  unfold accepted at checked
  split at checked
  · assumption
  · contradiction

private theorem bytes_equal (left right : ByteArray) (equal : (left == right) = true) : left = right := by
  change (left.data == right.data) = true at equal
  exact ByteArray.ext (by simpa only [beq_iff_eq] using equal)

/-- The adapter's accepted postcondition implies durability through every
admitted crash mask and fresh actual Rust repair, not merely write completion. -/
theorem acknowledged_crash (config : Concurrent.Config Term)
    (checked : accepted config = true) (mask : ByteArray) (image : Image) (rest : Term)
    (captured : crashImage ⟨2⟩ mask (snapshot config) = some image) :
    image.bytes = complete ∧
      repair_log ⟨image.highWater + 1⟩ 4#usize (restarted image (repairScript image.bytes rest)) =
        (.ok (.Ok (some (alloc.vec.Vec.from [13#u16,19#u16,23#u16] (by scalar_tac))), ⟨image.highWater + 1⟩),
          fileEnv ({} : Environment) ⟨image.highWater + 1⟩
            ⟨complete,complete,image.bytes.size,rest⟩ []) := by
  unfold accepted at checked
  split at checked
  · unfold stateAccepted at checked
    split at checked
    · rename_i file found
      simp only [Bool.and_eq_true] at checked
      obtain ⟨⟨⟨⟨⟨v,d⟩,_⟩,_⟩,_⟩,_⟩ := checked
      unfold crashImage at captured
      rw [found] at captured
      change (persist file.durable file.visible mask).bind
        (fun bytes => some (⟨bytes, (snapshot config).nativeRefCounter⟩ : Image)) = some image at captured
      obtain ⟨bytes, persisted, equal⟩ := Option.bind_eq_some_iff.mp captured
      cases Option.some.inj equal
      rw [bytes_equal _ _ v, bytes_equal _ _ d] at persisted
      have same := persist_same complete mask bytes persisted
      refine ⟨same, ?_⟩
      apply Record.RepairCrashProperties.restart_repair [13#u16,19#u16,23#u16] _ rest 4#usize
      · rw [same]
        simpa only [complete, List.append_nil] using Record.RepairCrashProperties.log_image [13#u16,19#u16,23#u16] [] (by decide)
      · rw [same]; dsimp only; decide
      · decide
    · contradiction
  · contradiction

end Record.RepairingLogProperties
