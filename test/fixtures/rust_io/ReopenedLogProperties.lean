module
public import Record.Extraction.Funs
public import Record.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx io_native
namespace Record.ReopenedLogProperties
open NativeFile
@[expose] def fileName : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩
@[expose] def names : Names := [(fileName,1)]
@[expose] def torn : ByteArray := ⟨#[13,0,242,255,99,0]⟩
@[expose] def repaired : ByteArray := ⟨#[13,0,242,255]⟩
@[expose] def zeros6 : ByteArray := ⟨#[0,0,0,0,0,0]⟩
@[expose] def action (operation : String) (count : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation,.atom "ok",.integer count,.bitstring zeros6 0]) rest
@[expose] def fileScript : Term := action "seek" 0
  (action "read" 1 (action "read" 1 (action "read" 1 (action "read" 1
    (action "read" 1 (action "read" 1 (action "read" 0
      (action "set_len" 0 (action "sync_all" 0 .nil)))))))))
@[expose] def initial : Environment := {
  nativeRefCounter := 1
  nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource]
  nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨names,names,[],
      .cons (.tuple #[.atom "open",.bitstring fileName 0,.atom "ok",.integer 0,fileScript]) .nil⟩),
    (1,inodeTypeName,encode ⟨torn,torn,0,.nil⟩)] }
@[expose] def accepted (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.nativeReference 7) =>
    let env := match config with
      | .start env _ => env
      | .running state .. => state.nativeView []
    match lookup ⟨2⟩ env with
    | some file =>
      let payload : shared_log.LogResource := ⟨⟨3⟩⟩
      file.visible.data == repaired.data && file.durable.data == repaired.data &&
      file.position == 6 && env.nativeRefCounter == 7 &&
      (NativeResourceArc.vmCells payload 4 6 7).all (fun cell => env.nativeHeap.contains cell) &&
      !env.nativeHeap.any (fun cell => cell.1 == 5) &&
      env.nativeHeap.contains (3,NativeMutex.typeName NativeFile,
        .tuple #[.atom "unlocked",.atom "unpoisoned",.nativeReference 2])
    | none => false
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
@[expose] def lawAccepted (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.atom "true") => true
  | _ => false

theorem accepted_outcome (config : Concurrent.Config Term)
    (accepted : lawAccepted config = true) : config.outcome = .ok Term.true := by
  unfold lawAccepted at accepted
  split at accepted
  · assumption
  · contradiction

end Record.ReopenedLogProperties
