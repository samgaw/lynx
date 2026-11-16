module
public import Lynx
public import LockedAwait.Properties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace LockedAwait.Io
open LockedAwait.Properties

@[expose] def action (success : Bool) (value : Nat) : Term :=
  .cons (.tuple #[.atom "write", .atom (if success then "ok" else "error"),
    .integer value, .bitstring ⟨#[0]⟩ 0]) .nil
@[expose] def data : Bytes := Array.make 2#usize [7#u8, 8#u8]
@[expose] def fileState (success : Bool) : NativeFile.State :=
  ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, action success (if success then 1 else 3)⟩
@[expose] def updated (success : Bool) : NativeFile.State :=
  ⟨⟨if success then #[7] else #[1]⟩, ⟨#[1]⟩, if success then 1 else 0, .nil⟩
@[expose] def mutexContents (poisoned : Bool) : Term :=
  .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
    NativeCodec.encode (⟨2⟩ : NativeFile)]
@[expose] def before (success poisoned : Bool) : Environment := {
  nativeRefCounter := if success then 2 else 3
  nativeHeap := [(1, NativeMutex.typeName NativeFile, mutexContents poisoned),
    (2, NativeFile.typeName, NativeFile.encode (fileState success))] ++
    if success then [] else [(3, NativeIoError.typeName, .atom "live")] }
@[expose] def acquired (success poisoned : Bool) : Environment := {
  nativeRefCounter := if success then 3 else 4
  nativeHeap := [(1, NativeMutex.typeName NativeFile,
      NativeMutex.lockedContents [] (if success then 3 else 4) poisoned (⟨2⟩ : NativeFile)),
    (2, NativeFile.typeName, NativeFile.encode (fileState success))] ++
    if success then [] else [(3, NativeIoError.typeName, .atom "live")] }
@[expose] def written (success poisoned : Bool) : Environment := {
  acquired success poisoned with
  nativeHeap := [(1, NativeMutex.typeName NativeFile,
      NativeMutex.lockedContents [] (if success then 3 else 4) poisoned (⟨2⟩ : NativeFile)),
    (2, NativeFile.typeName, NativeFile.encode (updated success))] ++
    if success then [] else [(3, NativeIoError.typeName, .atom "live")] }
@[expose] def cleaned (poisoned : Bool) : Environment := {
  written false poisoned with
  nativeHeap := [(1, NativeMutex.typeName NativeFile,
      NativeMutex.lockedContents [] 4 poisoned (⟨2⟩ : NativeFile)),
    (2, NativeFile.typeName, NativeFile.encode (updated false))] }
@[expose] def released (success poisoned : Bool) : Environment := {
  nativeRefCounter := if success then 3 else 4
  nativeHeap := [(1, NativeMutex.typeName NativeFile, mutexContents poisoned),
    (2, NativeFile.typeName, NativeFile.encode (updated success))] }
@[expose] def acquisition (success poisoned : Bool) :
    core.result.Result (NativeGuard NativeFile) (NativePoisonError (NativeGuard NativeFile)) :=
  let guard : NativeGuard NativeFile := ⟨⟨1⟩, if success then 3 else 4, [], ⟨2⟩⟩
  if poisoned then .Err ⟨guard⟩ else .Ok guard

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem partial_prefix (resume poisoned : Bool) :
    Result.ReadyPrefix (poll_locked_write ⟨1⟩ data resume) (before true poisoned)
      (.ok (if resume then some (.Ok 1#usize) else none)) (released true poisoned) := by
  apply caller_success_prefix (acquired := acquisition true poisoned)
    (locked := acquired true poisoned) (written := written true poisoned) (file := ⟨2⟩)
  · cases poisoned <;> cbv
  · cases poisoned <;> cbv
  · cases poisoned <;> cbv

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem error_prefix (resume poisoned : Bool) :
    Result.ReadyPrefix (poll_locked_write ⟨1⟩ data resume) (before false poisoned)
      (.ok (if resume then some (.Err 1#u8) else none)) (released false poisoned) := by
  apply caller_error_prefix (acquired := acquisition false poisoned) (error := .os 3)
    (locked := acquired false poisoned) (written := written false poisoned)
    (cleaned := cleaned poisoned) (file := ⟨2⟩)
  · cases poisoned <;> cbv
  · cases poisoned <;> cbv
  · unfold NativeIoError.dispose Result.consumeNativeCapability
    apply Result.ReadyPrefix.wait _ _ (.ok ()) (written false poisoned) (cleaned poisoned) _ _
    · cases poisoned <;> cbv
    · exact .refl _ _
  · cases poisoned <;> cbv

theorem partial_result (resume poisoned : Bool) :
    poll_locked_write ⟨1⟩ data resume (before true poisoned) =
      (.ok (if resume then some (.Ok 1#usize) else none), released true poisoned) := by
  simpa only [Result.ok_apply] using (partial_prefix resume poisoned).apply

theorem error_result (resume poisoned : Bool) :
    poll_locked_write ⟨1⟩ data resume (before false poisoned) =
      (.ok (if resume then some (.Err 1#u8) else none), released false poisoned) := by
  simpa only [Result.ok_apply] using (error_prefix resume poisoned).apply

end LockedAwait.Io
