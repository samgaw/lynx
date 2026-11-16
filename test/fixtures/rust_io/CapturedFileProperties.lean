module
public import Lynx
public import CapturedFile.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace CapturedFile.Properties
open NativeFile
abbrev Reply := core.result.Result Usize U8

theorem write_contract (file : NativeFile) (data : Slice U8) (accepted : Bool) :
    checked_write file data accepted = (do
      let (reply, returned) ← io_core.write_once file data
      let result : Reply ← match reply with
        | .Ok written => NativeM.ok (.Ok written)
        | .Err error => do
          NativeIoError.dispose error
          NativeM.ok (.Err 1#u8)
      NativeFile.close returned
      NativeM.ok (if accepted then .Ok result else .Err ())) := by
  simp only [checked_write, monadLift_self]
  congr 1
  funext returned
  rcases returned with ⟨reply, file⟩
  cases reply <;> cases accepted <;>
    simp [io_core.require_write, NativeOwnedDrop.drop, NativeResourceUnwindDrop.drop, NativeM.ok]

theorem error_contract (error : NativeIoError) (accepted : Bool) :
    checked_error error accepted = (do
      NativeIoError.dispose error
      NativeM.ok (if accepted then .Ok () else .Err ())) := by
  cases accepted <;>
    simp [checked_error, io_core.require_write, NativeOwnedDrop.drop,
      NativeResourceUnwindDrop.drop, NativeM.ok]

theorem mutex_contract (file : NativeFile) (accepted : Bool) :
    checked_file_mutex file accepted = (do
      let mutex ← NativeMutex.new file
      NativeMutex.disposeFile mutex
      NativeM.ok (if accepted then .Ok () else .Err ())) := by
  cases accepted <;>
    simp [checked_file_mutex, io_core.require_write, NativeOwnedDrop.drop,
      NativeResourceUnwindDrop.drop, NativeM.ok]

theorem write_ready (file : NativeFile) (data : Slice U8) (accepted : Bool) (count : Usize)
    (before written closed : Environment)
    (write : pollWrite file data before = some (.ok (.Ok count, file), written))
    (close : pollClose file written = some (.ok (), closed)) :
    checked_write file data accepted before =
      (.ok (if accepted then .Ok (.Ok count) else .Err ()), closed) := by
  rw [write_contract]
  simp only [io_core.write_once, monadLift_self, NativeFile.write, Result.wait_bind]
  rw [Result.wait_ready_run _ _ _ _ _ write]
  simp only [Result.ok_bind, NativeM.ok, NativeFile.close, Result.wait_bind]
  rw [Result.wait_ready_run _ _ _ _ _ close]
  simp

theorem admitted_error_cleanup (error : NativeIoError) (accepted : Bool) (env : Environment)
    (nonzero : error.identity ≠ 0) (bounded : error.identity ≤ env.nativeRefCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == error.identity) =
      [(error.identity, NativeIoError.typeName, .atom "live")]) :
    checked_error error accepted env = (.ok (if accepted then .Ok () else .Err ()),
      {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != error.identity)}) := by
  rw [error_contract]
  simp [NativeIoError.dispose, Result.consumeNativeCapability, nonzero, not_lt.mpr bounded,
    stored, NativeM.ok]

@[expose] def outcome (operation : String) (success : Bool) (value : Nat)
    (mask : ByteArray) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation, .atom (if success then "ok" else "error"),
    .integer value, .bitstring mask 0]) rest

@[expose] def input : Slice U8 := Slice.from [7#u8, 8#u8] (by scalar_tac)
@[expose] def script : Term :=
  outcome "write" true 1 ⟨#[0]⟩ (outcome "close" false 0 ⟨#[0]⟩ .nil)
@[expose] def initial : Environment :=
  {nativeRefCounter := 1, nativeHeap := [(1, typeName, encode ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, script⟩)]}
@[expose] def writtenState : Environment :=
  {nativeRefCounter := 1, nativeHeap := [(1, typeName,
    encode ⟨⟨#[7]⟩, ⟨#[1]⟩, 1, outcome "close" false 0 ⟨#[0]⟩ .nil⟩)]}
@[expose] def finished : Environment :=
  {nativeRefCounter := 1, nativeHeap := [(1, closedTypeName, encode ⟨⟨#[7]⟩, ⟨#[1]⟩, 1, .nil⟩)]}

theorem partial_write_and_panic (accepted : Bool) :
    checked_write ⟨1⟩ input accepted initial =
      (.ok (if accepted then .Ok (.Ok 1#usize) else .Err ()), finished) := by
  apply write_ready (written := writtenState)
  · cbv
  · cbv

theorem missing_error_cutoff (error : NativeIoError) (accepted : Bool) (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == error.identity) = []) :
    checked_error error accepted env = (.error .exhausted, env) := by
  rw [error_contract]
  simp [NativeIoError.dispose, Result.consumeNativeCapability, missing]

theorem custom_error_cutoff (error : NativeIoError) (accepted : Bool) (env : Environment)
    (custom : env.nativeHeap.filter (fun cell => cell.1 == error.identity) =
      [(error.identity, NativeIoError.typeName, .atom "custom")]) :
    checked_error error accepted env = (.error .exhausted, env) := by
  rw [error_contract]
  simp [NativeIoError.dispose, Result.consumeNativeCapability, custom]

@[expose] def mutexInitial : Environment :=
  {nativeRefCounter := 1, nativeHeap := [(1, typeName,
    encode ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, outcome "close" false 0 ⟨#[0]⟩ .nil⟩)]}
@[expose] def mutexFinished : Environment :=
  {nativeRefCounter := 2, nativeHeap := [(1, closedTypeName, encode ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, .nil⟩)]}

@[expose] def mutexRetired (accepted : Bool)
    (config : Concurrent.Config (core.result.Result Unit Unit)) : Bool :=
  let result := match config.outcome with
    | .ok (.Ok ()) => accepted
    | .ok (.Err ()) => !accepted
    | _ => false
  let env := match config with
    | .start env .. => env
    | .running state .. => state.nativeView []
  result && env.nativeRefCounter == mutexFinished.nativeRefCounter &&
    env.nativeHeap == mutexFinished.nativeHeap

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem mutex_panic_closes (accepted : Bool) :
    Concurrent.checkPost (mutexRetired accepted) 128
      (.start mutexInitial (checked_file_mutex ⟨1⟩ accepted)) = true := by
  set_option cbv.maxSteps 4000000 in cases accepted <;> cbv

@[expose] def missingClose : Environment :=
  {nativeRefCounter := 1, nativeHeap := [(1, typeName,
    encode ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, outcome "write" true 1 ⟨#[0]⟩ .nil⟩)]}
@[expose] def unclosed : Environment :=
  {nativeRefCounter := 1, nativeHeap := [(1, typeName, encode ⟨⟨#[7]⟩, ⟨#[1]⟩, 1, .nil⟩)]}

@[expose] def cutoffRetains (config : Concurrent.Config (core.result.Result Reply Unit)) : Bool :=
  let exhausted := match config.outcome with
    | .error .exhausted => true
    | _ => false
  let env := match config with
    | .start env .. => env
    | .running state .. => state.nativeView []
  exhausted && env.nativeRefCounter == unclosed.nativeRefCounter && env.nativeHeap == unclosed.nativeHeap

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem missing_close_cutoff (accepted : Bool) :
    Concurrent.checkPost cutoffRetains 128
      (.start missingClose (checked_write ⟨1⟩ input accepted)) = true := by
  set_option cbv.maxSteps 4000000 in cases accepted <;> cbv

end CapturedFile.Properties
