module
public import Record.LockedPrefixInvariant
public import Record.RecoveryPrefixWitness
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.LockedPrefixWitness
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties Record.RecoveryProperties
open Record.RecoveryPrefixWitness (image repaired script)

@[expose] def frame : List (Nat × String × Term) :=
  [(4,NativeIoError.typeName,.atom "live"),(7,"fixture:unrelated",.atom "preserved")]
@[expose] def initial (poisoned : Bool) (choices : Term) : Environment :=
  Record.LockedPrefixInvariant.view {} 9 frame (Record.LockedPrefixInvariant.free poisoned)
    ⟨image,image,5,choices⟩
@[expose] def effects (poisoned locked : Bool) (visible durable : ByteArray) (position : Nat)
    (config : Concurrent.Config (core.result.Result Bool NativeIoError)) : Bool :=
  let env := Record.RepairAppendAcknowledgement.snapshot [] config
  match lookup ⟨2⟩ env with
  | some state => state.visible == visible && state.durable == durable && state.position == position &&
      env.nativeRefCounter == 10 && frame.all env.nativeHeap.contains &&
      env.nativeHeap.contains (1,NativeMutex.typeName NativeFile,
        if locked then Record.LockedPrefixInvariant.held {} 9 poisoned else Record.LockedPrefixInvariant.free poisoned)
  | none => false
@[expose] def failed (visible durable : ByteArray) (position : Nat)
    (config : Concurrent.Config (core.result.Result Bool NativeIoError)) : Bool :=
  match config.outcome with
  | .ok (.Err error) => error.identity == 4 && effects true false visible durable position config
  | _ => false
@[expose] def capped (config : Concurrent.Config (core.result.Result Bool NativeIoError)) : Bool :=
  match config.outcome with
  | .ok (.Ok false) => effects false false image image 0 config
  | _ => false
@[expose] def blocked (config : Concurrent.Config (core.result.Result Bool NativeIoError)) : Bool :=
  match config.outcome with
  | .deadlock => effects true true repaired image 12 config
  | _ => false
@[expose] def complete : ByteArray := disk (logBytes [13#u16,19#u16,23#u16])
@[expose] def accepted (config : Concurrent.Config (core.result.Result Bool NativeIoError)) : Bool :=
  match config.outcome with
  | .ok (.Ok true) => effects true false complete complete 12 config
  | _ => false

set_option maxRecDepth 8192 in
/-- Poison recovery retains the actual guard, commits the extra valid record
and new payload, then releases without consuming unrelated cells. -/
theorem poisoned_success : Concurrent.checkPost accepted 512
    (.start (initial true (script 12 (outcome "set_len" true 0 (zeroMask image)
      (outcome "sync_all" true 0 ByteArray.empty (outcome "seek" true 0 (zeroMask repaired)
        (outcome "write" true 4 (zeroMask repaired) (outcome "sync_all" true 0 ByteArray.empty .nil)))))))
      (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- Partial read errors release the poisoned mutex and keep the actual cursor. -/
theorem read_error_releases : Concurrent.checkPost (failed image image 5) 256
    (.start (initial true (script 5 (outcome "read" false 4 (zeroMask image) .nil)))
      (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- A failed sync retains visible truncation and old durable suffix on release. -/
theorem sync_error_releases : Concurrent.checkPost (failed repaired image 12) 256
    (.start (initial true (script 12 (outcome "set_len" true 0 (zeroMask image)
      (outcome "sync_all" false 4 (zeroMask image) .nil))))
      (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- A cap returns false, not an append acknowledgement, and releases the guard. -/
theorem capped_releases : Concurrent.checkPost capped 256
    (.start (initial false (outcome "seek" true 0 (zeroMask image) .nil))
      (locked_repair_and_append ⟨1⟩ 0#usize 23#u16)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- Blocking before sync retains the owned mutex, distinct images and cursor;
no release or successful return is fabricated for the blocked invocation. -/
theorem blocked_keeps_guard : Concurrent.checkPost blocked 256
    (.start (initial true (script 12 (outcome "set_len" true 0 (zeroMask image)
      (.cons (.atom "blocked") .nil)))) (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) = true := by
  cbv

end Record.LockedPrefixWitness
