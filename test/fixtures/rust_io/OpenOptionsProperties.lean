module
public import Lynx
public import Record.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.OpenOptionsProperties
open NativeFile

/-- The actual Rust builder requests both permissions and preserves file contents. -/
theorem core_mode (path : Str) : io_core.open_readwrite path = NativeFile.openReadWrite path := by
  rfl

/-- The protocol crate calls the proved low-level implementation. -/
theorem composition (path : Str) : io_protocol.open_readwrite path = NativeFile.openReadWrite path := by
  simpa only [io_protocol.open_readwrite,monadLift_self] using core_mode path

@[expose] def fileName : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩
@[expose] def names : Names := [(fileName,1)]
@[expose] def before : ByteArray := ⟨#[13,0,242,255]⟩
@[expose] def after : ByteArray := ⟨#[13,0,242,255,19,0,236,255]⟩
@[expose] def zeros4 : ByteArray := ⟨#[0,0,0,0]⟩
@[expose] def zeros8 : ByteArray := ⟨#[0,0,0,0,0,0,0,0]⟩
@[expose] def action (operation : String) (count : Nat) (mask : ByteArray) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation,.atom "ok",.integer count,.bitstring mask 0]) rest
@[expose] def fileScript : Term := action "seek" 0 zeros4
  (action "write" 4 zeros8 (action "sync_all" 0 zeros8 (action "close" 0 zeros8 .nil)))
@[expose] def opening (script : Term) : Term :=
  .cons (.tuple #[.atom "open",.bitstring fileName 0,.atom "ok",.integer 0,script]) .nil
@[expose] def initial : Environment := {
  nativeRefCounter := 1
  nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨names,names,[],opening fileScript⟩),
    (1,inodeTypeName,encode ⟨before,before,0,.nil⟩)] }
/-- The real native caller must acknowledge both the old and new durable bytes,
retain the synchronized name, and consume the descriptor on return. -/
@[expose] def retained (config : Concurrent.Config (core.result.Result Bool NativeIoError)) : Bool :=
  match config.outcome with
  | .ok (.Ok true) =>
    let env := match config with
      | .start env _ => env
      | .running state .. => state.nativeView []
    match inode 1 env, namespaceSnapshot env with
    | some file, some snapshot =>
      file.visible.data == after.data && file.durable.data == after.data &&
      env.nativeRefCounter == 2 && (lookup ⟨2⟩ env).isNone &&
      namedInode snapshot.names fileName == some 1 &&
      namedInode snapshot.committed fileName == some 1
    | _, _ => false
  | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- Check the actual cross-crate Rust opener, append, sync and owned destructor. -/
theorem caller_checked : Concurrent.checkPost retained 128
    (.start initial (reopen_then_append (toStr "journal") 19#u16)) = true := by
  set_option cbv.maxSteps 4000000 in cbv

/-- Every terminal execution of this native Rust computation satisfies the
checked durable-file and descriptor-retirement postcondition. -/
theorem caller_every_run
    (run : Concurrent.Run (.start initial (reopen_then_append (toStr "journal") 19#u16)) events last)
    (terminal : Concurrent.Terminal last outcome) : retained last = true :=
  Concurrent.checkPost_sound caller_checked run terminal

@[expose] def scanScript : Term := action "seek" 0 zeros4
  (action "read" 1 zeros4 (action "read" 1 zeros4
    (action "read" 1 zeros4 (action "read" 1 zeros4
      (action "read" 0 zeros4 (action "close" 0 zeros4 .nil))))))
@[expose] def scanInitial : Environment := {
  nativeRefCounter := 1
  nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨names,names,[],opening scanScript⟩),
    (1,inodeTypeName,encode ⟨before,before,0,.nil⟩)] }

/-- Recovery must return the decoded record and close its owned descriptor
without changing either visible or durable bytes. -/
@[expose] def recovered
    (config : Concurrent.Config (core.result.Result (alloc.vec.Vec U16) NativeIoError)) : Bool :=
  match config.outcome with
  | .ok (.Ok values) =>
    let env := match config with
      | .start env _ => env
      | .running state .. => state.nativeView []
    match inode 1 env with
    | some file =>
      values.val == [13#u16] && file.visible.data == before.data &&
      file.durable.data == before.data && env.nativeRefCounter == 2 &&
      (lookup ⟨2⟩ env).isNone
    | none => false
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem recovery_checked : Concurrent.checkPost recovered 256
    (.start scanInitial (reopen_then_recover (toStr "journal") 2#usize)) = true := by
  set_option cbv.maxSteps 8000000 in cbv

theorem recovery_every_run
    (run : Concurrent.Run
      (.start scanInitial (reopen_then_recover (toStr "journal") 2#usize)) events last)
    (terminal : Concurrent.Terminal last outcome) : recovered last = true :=
  Concurrent.checkPost_sound recovery_checked run terminal

@[expose] def readFailureScript : Term := action "seek" 0 zeros4
  (.cons (.tuple #[.atom "read",.atom "error",.integer 7,.bitstring zeros4 0])
    (action "close" 0 zeros4 .nil))
@[expose] def failureInitial : Environment := {
  nativeRefCounter := 1
  nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨names,names,[],opening readFailureScript⟩),
    (1,inodeTypeName,encode ⟨before,before,0,.nil⟩)] }

/-- A real parser error must propagate after closing the caller's file. -/
@[expose] def rejected
    (config : Concurrent.Config (core.result.Result (alloc.vec.Vec U16) NativeIoError)) : Bool :=
  match config.outcome with
  | .ok (.Err error) =>
    let env := match config with
      | .start env _ => env
      | .running state .. => state.nativeView []
    match inode 1 env with
    | some file =>
      error.identity == 7 && file.visible.data == before.data &&
      file.durable.data == before.data && env.nativeRefCounter == 2 &&
      (lookup ⟨2⟩ env).isNone
    | none => false
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem failure_checked : Concurrent.checkPost rejected 256
    (.start failureInitial (reopen_then_recover (toStr "journal") 2#usize)) = true := by
  set_option cbv.maxSteps 8000000 in cbv

theorem failure_every_run
    (run : Concurrent.Run
      (.start failureInitial (reopen_then_recover (toStr "journal") 2#usize)) events last)
    (terminal : Concurrent.Terminal last outcome) : rejected last = true :=
  Concurrent.checkPost_sound failure_checked run terminal

end Record.OpenOptionsProperties
