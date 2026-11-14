module
public import Record.FileReturnIdentity
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.LockedPrefixInvariant
variable [heapLayout : Record.Properties.HeapLayout]
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.CrashProperties Record.LogProperties Record.ResizeProperties Record.RepairCrashProperties
  Record.AppendPrefixInvariant Record.LockedProperties

@[expose] def free (poisoned : Bool) : Term :=
  .tuple #[.atom "unlocked",.atom (if poisoned then "poisoned" else "unpoisoned"),.nativeReference 2]
@[expose] def held (base : Environment) (counter : Nat) (poisoned : Bool) : Term :=
  NativeMutex.lockedContents base.currentPid (counter + 1) poisoned (⟨2⟩ : NativeFile)
@[expose] def guard (base : Environment) (counter : Nat) : NativeGuard NativeFile :=
  ⟨⟨1⟩,counter + 1,base.currentPid,⟨2⟩⟩
@[expose] def view (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (state : State) : Environment :=
  fileEnv {base with nativeRefCounter := counter} ⟨2⟩ state
    ((1,NativeMutex.typeName NativeFile,contents) :: frame)

/-- The actual file, unrelated cells and all base fields survive acquisition,
body execution and release. Only the acquisition token, lock phase and admitted
file state may change; both images retain the known prefix. -/
@[expose] def Holds (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (poisoned : Bool) (head : ByteArray) (world : Environment) : Prop :=
  ∃ state, Admitted state ∧ Prefix head state.visible ∧ Prefix head state.durable ∧
    (world = view base counter frame (free poisoned) state ∨
      world = view base (counter + 1) frame (held base counter poisoned) state ∨
      world = view base (counter + 1) frame (free poisoned) state)

omit heapLayout in
private theorem filter_apart (id : Nat) (frame : List (Nat × String × Term))
    (apart : Separate (⟨id⟩ : NativeFile) frame) : frame.filter (fun cell => cell.1 == id) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro cell member
  simpa using apart cell member

omit heapLayout in
private theorem map_apart (id : Nat) (replacement : Nat × String × Term) (frame : List (Nat × String × Term))
    (apart : Separate (⟨id⟩ : NativeFile) frame) :
    frame.map (fun cell => if cell.1 = id then replacement else cell) = frame := by
  conv_rhs => rw [← List.map_id frame]
  apply List.map_congr_left
  intro cell member
  simp [apart cell member]

private theorem lock_poll (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (poisoned : Bool) (state : State) (bound : 2 ≤ counter) (apart : Separate (⟨1⟩ : NativeFile) frame)
    (fresh : frame.any (fun cell => cell.1 == counter + 1) = false) :
    NativeMutex.pollLock (⟨1⟩ : NativeMutex NativeFile) (view base counter frame (free poisoned) state) =
      some (.ok (if poisoned then .Err ⟨guard base counter⟩ else .Ok (guard base counter)),
        view base (counter + 1) frame (held base counter poisoned) state) := by
  have acquired := NativeMutex.pollLock_unlocked (⟨1⟩ : NativeMutex NativeFile) (⟨2⟩ : NativeFile)
    poisoned (view base counter frame (free poisoned) state)
    (by simp [view,fileEnv,free,filter_apart 1 frame apart,NativeCodec.encode])
    (by simp [view,fileEnv,Nat.max_eq_left bound,fresh]; omega)
  simpa [view,fileEnv,Nat.max_eq_left bound,held,guard,map_apart 1 _ frame apart,
    show max (counter + 1) 2 = counter + 1 by omega] using acquired

private theorem release_poll (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (poisoned : Bool) (state : State) (apart : Separate (⟨1⟩ : NativeFile) frame) :
    NativeGuard.pollRelease (guard base counter)
      (view base (counter + 1) frame (held base counter poisoned) state) =
      some (.ok (),view base (counter + 1) frame (free poisoned) state) := by
  cases poisoned <;> simp [NativeGuard.pollRelease,view,fileEnv,free,held,guard,
    filter_apart 1 frame apart,map_apart 1 _ frame apart,NativeMutex.lockedContents,NativeCodec.encode,NativeCodec.decode]

/-- The actual Rust guard covers every repair/append step and is released with
the actual returned file on all Rust result branches. Arbitrary suffixes, host
scripts, poison state and unrelated resource cells are admitted. Native failure,
blocking and exhaustion retain their actual phase rather than becoming success. -/
theorem critical_invariant_general (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (poisoned : Bool) (before : State) (values : List U16) (maximum : Usize) (value : U16)
    (bound : 2 ≤ counter) (mutexApart : Separate (⟨1⟩ : NativeFile) frame) (fileApart : Separate (⟨2⟩ : NativeFile) frame)
    (fresh : frame.any (fun cell => cell.1 == counter + 1) = false)
    (valid : Admitted before) (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Holds base counter frame poisoned (disk (logBytes values)))
      (locked_repair_and_append ⟨1⟩ maximum value) (view base counter frame (free poisoned) before) := by
  have separate : Separate (⟨2⟩ : NativeFile)
      ((1,NativeMutex.typeName NativeFile,held base counter poisoned) :: frame) := by
    simp only [Separate,List.mem_cons,forall_eq_or_imp]
    exact ⟨by decide,fileApart⟩
  have body := Record.RepairVisibleInvariant.repair_append_invariant
    {base with nativeRefCounter := counter + 1} ⟨2⟩
    ((1,NativeMutex.typeName NativeFile,held base counter poisoned) :: frame)
    values before maximum value separate valid durable visible
  have weakened : Result.NativeInvariant (Holds base counter frame poisoned (disk (logBytes values)))
      (repair_and_append ⟨2⟩ maximum value) (view base (counter + 1) frame (held base counter poisoned) before) := by
    intro residual world trace
    obtain ⟨⟨state,rfl,admitted,v,d⟩,fragment⟩ := body residual world trace
    exact ⟨⟨state,admitted,v,d,.inr (.inl rfl)⟩,fragment⟩
  rw [Record.RepairWriterProperties.critical_contract]
  simp only [NativeMutex.lock,Result.wait_bind]
  apply Result.NativeInvariant.wait _ _ _ ⟨before,valid,visible,durable,.inl rfl⟩
  intro actual world ready
  rw [lock_poll base counter frame poisoned before bound mutexApart fresh] at ready
  obtain ⟨rfl,rfl⟩ := ready
  simp only [Result.ok_bind]
  have recovered : recoverGuard (if poisoned then .Err ⟨guard base counter⟩ else .Ok (guard base counter)) =
      guard base counter := by cases poisoned <;> rfl
  rw [recovered]
  change Result.NativeInvariant _ (repair_and_append ⟨2⟩ maximum value >>= _)
    (view base (counter + 1) frame (held base counter poisoned) before)
  apply Result.NativeInvariant.bind (computation := repair_and_append ⟨2⟩ maximum value) weakened
  intro output world completed
  obtain ⟨reply,returnedFile⟩ := output
  have identity := Record.FileReturnIdentity.repair_append_returns_general ⟨2⟩
    {base with nativeRefCounter := counter + 1}
    ((1,NativeMutex.typeName NativeFile,held base counter poisoned) :: frame)
    before maximum value reply returnedFile world separate valid completed
  subst returnedFile
  obtain ⟨state,rfl,admitted,v,d⟩ := (body _ _ completed).1
  simp only [NativeGuard.release,Result.wait_bind]
  apply Result.NativeInvariant.wait _ _ _ ⟨state,admitted,v,d,.inr (.inl rfl)⟩
  intro actual world ready
  change NativeGuard.pollRelease (guard base counter)
    (view base (counter + 1) frame (held base counter poisoned) state) = some (actual,world) at ready
  rw [release_poll base counter frame poisoned state mutexApart] at ready
  obtain ⟨rfl,rfl⟩ := ready
  simp only [Result.ok_bind]
  exact .ok _ _ _ ⟨state,admitted,v,d,.inr (.inr rfl)⟩

theorem critical_invariant (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (poisoned : Bool) (before : State) (values : List U16) (maximum : Usize) (value : U16)
    (bound : 2 ≤ counter) (mutexApart : Separate (⟨1⟩ : NativeFile) frame) (fileApart : Separate (⟨2⟩ : NativeFile) frame)
    (fresh : frame.any (fun cell => cell.1 == counter + 1) = false)
    (valid : Admitted before) (stable : before.durable = before.visible)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Holds base counter frame poisoned (disk (logBytes values)))
      (locked_repair_and_append ⟨1⟩ maximum value) (view base counter frame (free poisoned) before) := by
  exact critical_invariant_general base counter frame poisoned before values maximum value
    bound mutexApart fileApart fresh valid (stable ▸ visible) visible

/-- Every actual Rust return releases the same file identity, including I/O
errors and capped/rollback false. Earlier mutations and the exact frame survive. -/
theorem critical_returns_general (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (poisoned : Bool) (before : State) (values : List U16) (maximum : Usize) (value : U16)
    (bound : 2 ≤ counter) (mutexApart : Separate (⟨1⟩ : NativeFile) frame) (fileApart : Separate (⟨2⟩ : NativeFile) frame)
    (fresh : frame.any (fun cell => cell.1 == counter + 1) = false)
    (valid : Admitted before) (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (reply : core.result.Result Bool NativeIoError) (world : Environment)
    (trace : Result.ReadyPrefix (locked_repair_and_append ⟨1⟩ maximum value)
      (view base counter frame (free poisoned) before) (.ok reply) world) :
    ∃ after, world = view base (counter + 1) frame (free poisoned) after ∧
      Admitted after ∧ Prefix (disk (logBytes values)) after.visible ∧ Prefix (disk (logBytes values)) after.durable := by
  rw [Record.RepairWriterProperties.critical_contract] at trace
  simp only [NativeMutex.lock,Result.wait_bind] at trace
  cases trace with
  | wait _ _ actual _ middle _ _ ready continuation =>
      rw [lock_poll base counter frame poisoned before bound mutexApart fresh] at ready
      obtain ⟨rfl,rfl⟩ := ready
      simp only [Result.ok_bind] at continuation
      have recovered : recoverGuard (if poisoned then .Err ⟨guard base counter⟩ else .Ok (guard base counter)) =
          guard base counter := by cases poisoned <;> rfl
      rw [recovered] at continuation
      change Result.ReadyPrefix (repair_and_append ⟨2⟩ maximum value >>= _)
        (view base (counter + 1) frame (held base counter poisoned) before) (.ok reply) world at continuation
      obtain ⟨⟨bodyReply,returnedFile⟩,middle,bodyTrace,continuation⟩ := continuation.bind_returns
      have separate : Separate (⟨2⟩ : NativeFile)
          ((1,NativeMutex.typeName NativeFile,held base counter poisoned) :: frame) := by
        simp only [Separate,List.mem_cons,forall_eq_or_imp]; exact ⟨by decide,fileApart⟩
      have identity := Record.FileReturnIdentity.repair_append_returns_general ⟨2⟩
        {base with nativeRefCounter := counter + 1} _ before maximum value bodyReply returnedFile middle
        separate valid bodyTrace
      subst returnedFile
      have safe := Record.RepairVisibleInvariant.repair_append_invariant
        {base with nativeRefCounter := counter + 1} ⟨2⟩ _ values before maximum value separate valid durable visible
      obtain ⟨after,rfl,admitted,v,d⟩ := (safe _ _ bodyTrace).1
      simp only [NativeGuard.release,Result.wait_bind] at continuation
      cases continuation with
      | wait _ _ actual _ middle _ _ ready continuation =>
          change NativeGuard.pollRelease (guard base counter)
            (view base (counter + 1) frame (held base counter poisoned) after) = some (actual,middle) at ready
          rw [release_poll base counter frame poisoned after mutexApart] at ready
          obtain ⟨rfl,rfl⟩ := ready
          simp only [Result.ok_bind,NativeM.ok] at continuation
          cases continuation
          exact ⟨after,rfl,admitted,v,d⟩

theorem critical_returns (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (poisoned : Bool) (before : State) (values : List U16) (maximum : Usize) (value : U16)
    (bound : 2 ≤ counter) (mutexApart : Separate (⟨1⟩ : NativeFile) frame) (fileApart : Separate (⟨2⟩ : NativeFile) frame)
    (fresh : frame.any (fun cell => cell.1 == counter + 1) = false)
    (valid : Admitted before) (stable : before.durable = before.visible)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (reply : core.result.Result Bool NativeIoError) (world : Environment)
    (trace : Result.ReadyPrefix (locked_repair_and_append ⟨1⟩ maximum value)
      (view base counter frame (free poisoned) before) (.ok reply) world) :
    ∃ after, world = view base (counter + 1) frame (free poisoned) after ∧
      Admitted after ∧ Prefix (disk (logBytes values)) after.visible ∧ Prefix (disk (logBytes values)) after.durable := by
  exact critical_returns_general base counter frame poisoned before values maximum value
    bound mutexApart fileApart fresh valid (stable ▸ visible) visible reply world trace

/-- Actual body execution retains the owned mutex token and prevents any peer
context from acquiring it. The host script and suffix are unrestricted. -/
theorem body_excludes_peer (base : Environment) (owner peer : PID) (token : Nat) (poisoned : Bool)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State) (maximum : Usize) (value : U16)
    (different : owner ≠ peer) (fileApart : Separate (⟨2⟩ : NativeFile) frame)
    (mutexApart : Separate (⟨1⟩ : NativeFile) frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (visible : Prefix (disk (logBytes values)) before.visible)
    (trace : Result.ReadyPrefix (repair_and_append ⟨2⟩ maximum value)
      (fileEnv base ⟨2⟩ before ((1,NativeMutex.typeName NativeFile,
        NativeMutex.lockedContents owner token poisoned (⟨2⟩ : NativeFile)) :: frame)) residual world) :
    NativeMutex.pollLock (⟨1⟩ : NativeMutex NativeFile) {world with currentPid := peer} = none := by
  have safe := Record.RepairAppendPrefixInvariant.repair_append_invariant base ⟨2⟩
    ((1,NativeMutex.typeName NativeFile,NativeMutex.lockedContents owner token poisoned (⟨2⟩ : NativeFile)) :: frame)
    values before maximum value (by simp [Separate] at fileApart ⊢; exact fileApart) valid stable visible
  obtain ⟨after,rfl,_⟩ := (safe _ _ trace).1
  cases poisoned <;> simp [NativeMutex.pollLock,fileEnv,NativeMutex.lockedContents,NativeMutex.typeName,
    NativeCodec.decode,NativeCodec.encode,NativeCodec.typeName,different,filter_apart 1 frame mutexApart]

/-- Every finite raw execution prefix retains the file prefix and actual mutex
phase, including a blocked wait. This is safety for one native invocation;
arbitrary interference by other running callers requires a separate composition. -/
theorem critical_prefix (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (poisoned : Bool) (before : State) (values : List U16) (maximum : Usize) (value : U16)
    (bound : 2 ≤ counter) (mutexApart : Separate (⟨1⟩ : NativeFile) frame) (fileApart : Separate (⟨2⟩ : NativeFile) frame)
    (fresh : frame.any (fun cell => cell.1 == counter + 1) = false)
    (valid : Admitted before) (stable : before.durable = before.visible)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config (core.result.Result Bool NativeIoError))
    (run : Concurrent.Run (.start (view base counter frame (free poisoned) before)
      (locked_repair_and_append ⟨1⟩ maximum value) elapsed) events last) :
    Holds base counter frame poisoned (disk (logBytes values))
      (Record.RepairAppendAcknowledgement.snapshot base.currentPid last) := by
  have safe := critical_invariant base counter frame poisoned before values maximum value
    bound mutexApart fileApart fresh valid stable visible
  obtain ⟨world,kept,current⟩ := safe.run elapsed run
  rcases current with ⟨residual,rfl⟩ | ⟨residual,rfl⟩
  · exact kept
  · have observed : (Concurrent.State.initial world elapsed).nativeView base.currentPid = world := by
      obtain ⟨state,_,_,_,phase⟩ := kept
      rcases phase with rfl | rfl | rfl <;>
        simp [Concurrent.State.nativeView,Concurrent.State.view,Concurrent.State.process,
          Concurrent.State.initial,view,fileEnv]
    simpa only [Record.RepairAppendAcknowledgement.snapshot,observed] using kept

/-- Every admitted crash of an actual wrapper prefix retains the known records,
which the actual capped Rust reader recovers under the fresh read admission.
No successful return, released mutex or new acknowledgement is assumed. -/
theorem crash_recovery (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (poisoned : Bool) (before : State) (values : List U16) (maximum : Usize) (value : U16)
    (bound : 2 ≤ counter) (mutexApart : Separate (⟨1⟩ : NativeFile) frame) (fileApart : Separate (⟨2⟩ : NativeFile) frame)
    (fresh : frame.any (fun cell => cell.1 == counter + 1) = false)
    (valid : Admitted before) (stable : before.durable = before.visible)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config (core.result.Result Bool NativeIoError))
    (run : Concurrent.Run (.start (view base counter frame (free poisoned) before)
      (locked_repair_and_append ⟨1⟩ maximum value) elapsed) events last)
    (mask : ByteArray) (image : Image) (rest : Term)
    (captured : crashImage ⟨2⟩ mask (Record.RepairAppendAcknowledgement.snapshot base.currentPid last) = some image) :
    ∃ (capacity : values.length ≤ 262144),
      recover_log ⟨image.highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
        (restarted image (recoveryScript image.bytes rest)) =
        (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)),⟨image.highWater + 1⟩),
          fileEnv ({} : Environment) ⟨image.highWater + 1⟩
            (scanning image.bytes rest (4 * values.length)) []) := by
  obtain ⟨state,admitted,v,d,phase⟩ := critical_prefix base counter frame poisoned before values maximum value
    bound mutexApart fileApart fresh valid stable visible elapsed events last run
  have recover (count : Nat) (contents : Term)
      (capture : crashImage ⟨2⟩ mask (view base count frame contents state) = some image) :=
    recover_prefix_image {base with nativeRefCounter := count} ⟨2⟩
      ((1,NativeMutex.typeName NativeFile,contents) :: frame) values _
      (by simp [Separate] at fileApart ⊢; exact fileApart) ⟨state,rfl,admitted,v,d⟩ mask image rest capture
  rcases phase with observed | observed | observed
  · exact recover counter (free poisoned) (by rwa [← observed])
  · exact recover (counter + 1) (held base counter poisoned) (by rwa [← observed])
  · exact recover (counter + 1) (free poisoned) (by rwa [← observed])

end Record.LockedPrefixInvariant
