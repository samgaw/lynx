module
public import Lynx
public import GuardedSync.Properties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace GuardedSync.Io

@[expose] def data : Properties.Bytes := Array.make 2#usize [7#u8,8#u8]
@[expose] def action (operation : String) (success : Bool) (value : Nat)
    (mask : ByteArray) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation, .atom (if success then "ok" else "error"),
    .integer value, .bitstring mask 0]) rest
@[expose] def visible (short : Bool) : ByteArray := if short then ⟨#[7]⟩ else ⟨#[7,8]⟩
@[expose] def syncChoice (failed persisted : Bool) : Term :=
  action "sync_all" (!failed) (if failed then 3 else 0)
    ⟨#[if persisted then 1 else 0]⟩ .nil
@[expose] def mutex : Term := .tuple #[.atom "unlocked", .atom "unpoisoned",
  NativeCodec.encode (⟨2⟩ : NativeFile)]
@[expose] def state (counter : Nat) (file : NativeFile.State) (errors : List Nat) : Environment := {
  nativeRefCounter := counter
  nativeHeap := [(1, NativeMutex.typeName NativeFile, mutex),
    (2, NativeFile.typeName, NativeFile.encode file)] ++
    errors.map (fun id => (id, NativeIoError.typeName, .atom "live")) }
@[expose] def before (failed persisted short : Bool) : Environment :=
  state (if failed then 3 else 2)
    ⟨⟨#[1]⟩, ⟨#[1]⟩, 0,
      action "write" true (if short then 1 else 2) ⟨#[0]⟩ (syncChoice failed persisted)⟩
    (if failed then [3] else [])
@[expose] def after (resume failed persisted short : Bool) : Environment :=
  state (if failed then 4 else 3)
    ⟨visible short,
      if resume then (if failed then (if persisted then ⟨#[7]⟩ else ⟨#[1]⟩) else visible short)
      else ⟨#[1]⟩,
      if short then 1 else 2,
      if resume then .nil else syncChoice failed persisted⟩
    (if failed && !resume then [3] else [])
@[expose] def accept (resume failed persisted short : Bool)
    (config : Concurrent.Config (Option Properties.Reply)) : Bool :=
  let returned := match config.outcome with
    | .ok none => !resume
    | .ok (some (.Ok count)) => resume && !failed && count.val == (if short then 1 else 2)
    | .ok (some (.Err code)) => resume && failed && code.val == 2
    | _ => false
  let env := match config with | .start env .. => env | .running runtime .. => runtime.nativeView []
  returned && env.nativeRefCounter == (after resume failed persisted short).nativeRefCounter &&
    env.nativeHeap == (after resume failed persisted short).nativeHeap

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem cancel_and_sync_outcomes (resume failed persisted short : Bool) :
    Concurrent.checkPost (accept resume failed persisted short) 512
      (.start (before failed persisted short) (poll_locked_sync ⟨1⟩ data resume)) = true := by
  simp only [Properties.caller_contract, Properties.synchronize_contract,
    io_core.write_once, monadLift_self]
  set_option cbv.maxSteps 32000000 in
  cases resume <;> cases failed <;> cases persisted <;> cases short <;> cbv

theorem every_completed_call (resume failed persisted short : Bool)
    (run : Concurrent.Run (.start (before failed persisted short)
      (poll_locked_sync ⟨1⟩ data resume)) events last)
    (terminal : Concurrent.Terminal last outcome) : accept resume failed persisted short last = true :=
  Concurrent.checkPost_sound (cancel_and_sync_outcomes resume failed persisted short) run terminal

@[expose] def writeErrorBefore : Environment := state 3
  ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, action "write" false 3 ⟨#[0]⟩ (syncChoice false false)⟩ [3]
@[expose] def writeErrorAfter : Environment := state 4
  ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, syncChoice false false⟩ []
@[expose] def acceptWriteError (resume : Bool)
    (config : Concurrent.Config (Option Properties.Reply)) : Bool :=
  let returned := match config.outcome with
    | .ok none => !resume
    | .ok (some (.Err code)) => resume && code.val == 1
    | _ => false
  let env := match config with | .start env .. => env | .running runtime .. => runtime.nativeView []
  returned && env.nativeRefCounter == 4 && env.nativeHeap == writeErrorAfter.nativeHeap

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem write_error_skips_sync (resume : Bool) :
    Concurrent.checkPost (acceptWriteError resume) 512
      (.start writeErrorBefore (poll_locked_sync ⟨1⟩ data resume)) = true := by
  simp only [Properties.caller_contract, Properties.synchronize_contract,
    io_core.write_once, monadLift_self]
  cases resume <;> cbv

end GuardedSync.Io
