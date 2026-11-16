module
public import Lynx
public import GuardedRecovery.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace GuardedRecovery.Properties

@[expose] def fileName : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩
@[expose] def names : NativeFile.Names := [(fileName, 1)]
@[expose] def bytes (complete : Bool) : ByteArray :=
  if complete then ⟨#[7,8,9,10]⟩ else ⟨#[1]⟩
@[expose] def mask (complete : Bool) : ByteArray :=
  if complete then ⟨#[0,0,0,0]⟩ else ⟨#[0]⟩
@[expose] def action (operation : String) (count : Nat) (complete : Bool) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation, .atom "ok", .integer count,
    .bitstring (mask complete) 0]) rest
@[expose] def reads (complete : Bool) : Term :=
  action "seek" 0 complete (action "read" 1 complete
    (action "read" (if complete then 1 else 0) complete
      (action "seek" 0 complete (action "read" (if complete then 1 else 0) complete
        (if complete then action "read" 1 complete (action "close" 0 complete .nil)
        else action "close" 0 complete .nil)))))
@[expose] def opening (complete : Bool) : Term :=
  .cons (.tuple #[.atom "open", .bitstring fileName 0, .atom "ok", .integer 0,
    reads complete]) .nil
@[expose] def image (complete : Bool) : NativeFile.FilesystemImage :=
  ⟨names, [(1,bytes complete)], 6⟩
@[expose] def boot (complete : Bool) : Environment := {
  nativeRefCounter := 6
  nativeHeap := [
    (0, NativeFile.namespaceTypeName,
      NativeFile.encodeNamespace ⟨names,names,[],opening complete⟩),
    (1, NativeFile.inodeTypeName,
      NativeFile.encode ⟨bytes complete,bytes complete,0,.nil⟩)] }
@[expose] def after (complete : Bool) : Environment := {
  nativeRefCounter := 10
  nativeHeap := [
    (7, NativeFile.closedHandleTypeName,
      NativeFile.encodeHandle ⟨1,(if complete then 4 else 2),.nil⟩),
    (0, NativeFile.namespaceTypeName, NativeFile.encodeNamespace ⟨names,names,[],.nil⟩),
    (1, NativeFile.inodeTypeName,
      NativeFile.encode ⟨bytes complete,bytes complete,0,.nil⟩)] }
@[expose] def recovered (complete : Bool)
    (config : Concurrent.Config (core.result.Result (Option U16 × Option U16) U8)) : Bool :=
  let returned := match config.outcome with
    | .ok (.Ok (some first,some second)) => complete && first.val == 2055 && second.val == 2569
    | .ok (.Ok (none,none)) => !complete
    | _ => false
  let env := match config with | .start env .. => env | .running runtime .. => runtime.nativeView []
  returned && (Concurrent.nativeEnvironment env).identical
    (Concurrent.nativeEnvironment (after complete))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem recovery_after_restart (complete : Bool) :
    NativeFile.restartFilesystem (image complete) (opening complete) = some (boot complete) ∧
    Concurrent.checkPost (recovered complete) 1024
      (.start (boot complete) (reopen_words (toStr "journal"))) = true := by
  cases complete <;> constructor <;> cbv

theorem every_recovery (complete : Bool)
    (run : Concurrent.Run (.start (boot complete) (reopen_words (toStr "journal"))) events last)
    (terminal : Concurrent.Terminal last outcome) : recovered complete last = true :=
  Concurrent.checkPost_sound (recovery_after_restart complete).2 run terminal

end GuardedRecovery.Properties
