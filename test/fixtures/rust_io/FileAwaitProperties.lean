module
public import Lynx
public import FileAwait.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace FileAwait.Properties
abbrev Bytes := Array U8 2#usize
abbrev Reply := core.result.Result Usize U8
@[expose] def initial (file : NativeFile) (data : Bytes) : suspended_write.closure :=
  ⟨some file, data, 0#u32, none, none, none, none, none⟩
@[expose] def pending (file : NativeFile) (data : Bytes) (reply : Reply) : suspended_write.closure :=
  ⟨none, data, 3#u32, some file, some data, some reply, some ⟨false⟩, some true⟩
@[expose] def completed (data : Bytes) (reply : Reply) : suspended_write.closure :=
  ⟨none, data, 1#u32, none, some data, some reply, some ⟨false⟩, some false⟩

theorem constructor (file : NativeFile) (data : Bytes) :
    suspended_write file data = NativeM.ok (initial file data) := rfl

theorem unstarted_cleanup (file : NativeFile) (data : Bytes) :
    suspended_write.closure.drop_owned (initial file data) = NativeFile.close file := by
  simp [suspended_write.closure.drop_owned, initial, NativeOwnedDrop.drop, UScalar.ofNatCore]

theorem suspended_cleanup (file : NativeFile) (data : Bytes) (reply : Reply) :
    suspended_write.closure.drop_owned (pending file data reply) = NativeFile.close file := by
  simp [suspended_write.closure.drop_owned, pending, NativeOwnedDrop.drop, UScalar.ofNatCore]

theorem completed_cleanup (data : Bytes) (reply : Reply) :
    suspended_write.closure.drop_owned (completed data reply) = NativeM.ok () := by
  simp [suspended_write.closure.drop_owned, completed, NativeM.ok, UScalar.ofNatCore]

theorem yield_pending (context : NativeTaskContext) :
    io_core.YieldOnce.Insts.CoreFutureFutureFutureTuple.poll ⟨⟨true⟩⟩ context = (do
      NativeWaker.wakeByRef (NativeTaskContext.waker context)
      NativeM.ok (.Pending, ⟨⟨false⟩⟩, context)) := by
  simp [io_core.YieldOnce.Insts.CoreFutureFutureFutureTuple.poll,
    core.pin.PinMutAT.get_mut, NativeM.ok]

theorem yield_ready (context : NativeTaskContext) :
    io_core.YieldOnce.Insts.CoreFutureFutureFutureTuple.poll ⟨⟨false⟩⟩ context =
      NativeM.ok (.Ready (), ⟨⟨false⟩⟩, context) := by
  simp [io_core.YieldOnce.Insts.CoreFutureFutureFutureTuple.poll,
    core.pin.PinMutAT.get_mut, NativeM.ok]

theorem resume_contract (file : NativeFile) (data : Bytes) (reply : Reply)
    (context : NativeTaskContext) :
    suspended_write.closure.poll ⟨pending file data reply⟩ context = (do
      NativeFile.close file
      NativeM.ok (.Ready reply, ⟨completed data reply⟩, context)) := by
  simp [suspended_write.closure.poll, pending, completed,
    yield_ready, NativeOwnedDrop.drop, NativeM.ok, UScalar.ofNatCore]

theorem first_pending_contract (file : NativeFile) (data : Bytes)
    (context : NativeTaskContext) :
    suspended_write.closure.poll ⟨initial file data⟩ context = (do
      let (reply, returned) ← io_core.write_once file (Array.to_slice data)
      let result : Reply ← match reply with
        | .Ok count => NativeM.ok (.Ok count)
        | .Err error => do
          NativeIoError.dispose error
          NativeM.ok (.Err 1#u8)
      NativeWaker.wakeByRef (NativeTaskContext.waker context)
      NativeM.ok (.Pending, ⟨pending returned data result⟩, context)) := by
  simp [suspended_write.closure.poll, initial, UScalar.ofNatCore,
    NativeM.ok, NativeM.lift]
  congr 1
  funext returned
  rcases returned with ⟨reply, file⟩
  cases reply <;> simp [io_core.yield_once,
    core.future.into_future.IntoFuture.Blanket.into_future,
    yield_pending, NativeOwnedDrop.drop, NativeM.ok, pending, bind_assoc, UScalar.ofNatCore]

theorem first_ready (file : NativeFile) (data : Bytes) (count : Usize)
    (before written : Environment)
    (ready : NativeFile.pollWrite file (Array.to_slice data) before =
      some (.ok (.Ok count, file), written)) :
    suspended_write.closure.poll ⟨initial file data⟩ ⟨NativeWaker.noop⟩ before =
      (.ok (.Pending, ⟨pending file data (.Ok count)⟩, ⟨NativeWaker.noop⟩), written) := by
  rw [first_pending_contract]
  simp only [io_core.write_once, monadLift_self, NativeFile.write, Result.wait_bind]
  rw [Result.wait_ready_run _ _ _ _ _ ready]
  simp [NativeWaker.wakeByRef, NativeWaker.noop, NativeM.ok]

theorem cancellation_ready (file : NativeFile) (data : Bytes) (reply : Reply)
    (written closed : Environment)
    (ready : NativeFile.pollClose file written = some (.ok (), closed)) :
    suspended_write.closure.drop_owned (pending file data reply) written = (.ok (), closed) := by
  rw [suspended_cleanup]
  simp only [NativeFile.close]
  rw [Result.wait_ready_run _ _ _ _ _ ready]
  simp

theorem resume_ready (file : NativeFile) (data : Bytes) (reply : Reply)
    (context : NativeTaskContext) (written closed : Environment)
    (ready : NativeFile.pollClose file written = some (.ok (), closed)) :
    suspended_write.closure.poll ⟨pending file data reply⟩ context written =
      (.ok (.Ready reply, ⟨completed data reply⟩, context), closed) := by
  rw [resume_contract]
  simp only [NativeFile.close, Result.wait_bind]
  rw [Result.wait_ready_run _ _ _ _ _ ready]
  simp [NativeM.ok]

theorem caller_contract (file : NativeFile) (data : Bytes) (resume : Bool) :
    poll_write file data resume = (do
      let (reply, returned) ← io_core.write_once file (Array.to_slice data)
      let result : Reply ← match reply with
        | .Ok count => NativeM.ok (.Ok count)
        | .Err error => do
          NativeIoError.dispose error
          NativeM.ok (.Err 1#u8)
      NativeFile.close returned
      NativeM.ok (if resume then some result else none)) := by
  simp [poll_write, constructor, first_pending_contract,
    NativeTaskContext.fromWaker, NativeWaker.noop, NativeWaker.wakeByRef,
    NativeM.ok, bind_assoc]
  congr 1
  funext returned
  rcases returned with ⟨reply, file⟩
  cases reply <;> cases resume <;>
    simp [resume_contract, suspended_cleanup, completed_cleanup, NativeM.ok, bind_assoc]

theorem undefined_is_cutoff : (NativeM.fail .undef : NativeM Unit) = Result.error .exhausted := rfl

theorem caller_ready (file : NativeFile) (data : Bytes) (resume : Bool) (count : Usize)
    (before written closed : Environment)
    (write : NativeFile.pollWrite file (Array.to_slice data) before =
      some (.ok (.Ok count, file), written))
    (close : NativeFile.pollClose file written = some (.ok (), closed)) :
    poll_write file data resume before =
      (.ok (if resume then some (.Ok count) else none), closed) := by
  rw [caller_contract]
  simp only [io_core.write_once, monadLift_self, NativeFile.write, Result.wait_bind]
  rw [Result.wait_ready_run _ _ _ _ _ write]
  simp only [Result.ok_bind, NativeM.ok, NativeFile.close, Result.wait_bind]
  rw [Result.wait_ready_run _ _ _ _ _ close]
  simp

@[expose] def outcome (operation : String) (success : Bool) (value : Nat)
    (rest : Term) : Term :=
  .cons (.tuple #[.atom operation, .atom (if success then "ok" else "error"),
    .integer value, .bitstring ⟨#[0]⟩ 0]) rest
@[expose] def input : Bytes := Array.make 2#usize [7#u8, 8#u8]
@[expose] def before : Environment := {
  nativeRefCounter := 1
  nativeHeap := [(1, NativeFile.typeName, NativeFile.encode
    ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, outcome "write" true 1 (outcome "close" false 0 .nil)⟩)] }
@[expose] def written : Environment := {
  nativeRefCounter := 1
  nativeHeap := [(1, NativeFile.typeName, NativeFile.encode
    ⟨⟨#[7]⟩, ⟨#[1]⟩, 1, outcome "close" false 0 .nil⟩)] }
@[expose] def closed : Environment := {
  nativeRefCounter := 1
  nativeHeap := [(1, NativeFile.closedTypeName, NativeFile.encode
    ⟨⟨#[7]⟩, ⟨#[1]⟩, 1, .nil⟩)] }

theorem partial_write_before_pending :
    suspended_write.closure.poll ⟨initial ⟨1⟩ input⟩ ⟨NativeWaker.noop⟩ before =
      (.ok (.Pending, ⟨pending ⟨1⟩ input (.Ok 1#usize)⟩, ⟨NativeWaker.noop⟩), written) := by
  apply first_ready
  cbv

theorem cancellation_or_completion_retains_write (resume : Bool) :
    poll_write ⟨1⟩ input resume before =
      (.ok (if resume then some (.Ok 1#usize) else none), closed) := by
  apply caller_ready (written := written)
  · cbv
  · cbv

theorem repoll_completed_panics (data : Bytes) (reply : Reply) (context : NativeTaskContext) :
    suspended_write.closure.poll ⟨completed data reply⟩ context = NativeM.fail .panic := by
  simp [suspended_write.closure.poll, completed, UScalar.ofNatCore]

theorem invalid_cleanup_cutoff (file : NativeFile) (data : Bytes) :
    suspended_write.closure.drop_owned {initial file data with state := 99#u32} =
      NativeM.fail .undef := by
  simp [suspended_write.closure.drop_owned, initial, UScalar.ofNatCore]

theorem invalid_cleanup_never_succeeds (file : NativeFile) (data : Bytes) (env : Environment) :
    suspended_write.closure.drop_owned {initial file data with state := 99#u32} env =
      (.error .exhausted, env) := by
  rw [invalid_cleanup_cutoff]
  simp [NativeM.fail]

end FileAwait.Properties
