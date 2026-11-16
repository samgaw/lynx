module
public import GuardedRecovery.LockedCompleteness
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedRecovery.RecoveryCompleteness
open GuardedRecovery.RecoveryTrace

private theorem read_cell_returns {tag : String} {identity : Nat} {value : Term}
    {before after : Environment}
    (trace : Result.ReadyPrefix (NativeM.readCell tag identity) before (.ok value) after) :
    before.nativeHeap.filter (fun cell => cell.1 == identity) = [(identity,tag,value)] ∧ after = before := by
  simp only [NativeM.readCell] at trace
  cases trace with
  | nativeGet _ _ _ _ rest =>
    dsimp only at rest
    split at rest
    · rename_i storedIdentity storedType contents matching
      split at rest
      · rename_i sameType
        obtain ⟨rfl,rfl⟩ := rest.ok_returns
        have member : (storedIdentity,storedType,contents) ∈
            before.nativeHeap.filter (fun cell => cell.1 == identity) := by
          rw [matching]
          simp
        have sameIdentity : storedIdentity = identity := by
          simpa using (List.mem_filter.mp member).2
        have typeEqual : storedType = tag := by simpa using sameType
        exact ⟨by simpa [sameIdentity,typeEqual] using matching,rfl⟩
      · cases rest
    · cases rest

private theorem new_returns {file : NativeFile} {mutex : NativeMutex NativeFile}
    {before after : Environment}
    (trace : Result.ReadyPrefix (NativeMutex.new file) before (.ok mutex) after) :
    mutex = ⟨before.nativeRefCounter + 1⟩ ∧ after = initialized file before ∧
      before.nativeHeap.any (fun cell => cell.1 == before.nativeRefCounter + 1) = false := by
  simp only [NativeMutex.new] at trace
  obtain ⟨identity,middle,allocated,rest⟩ := trace.bind_returns
  simp only [NativeM.allocate] at allocated
  obtain ⟨response,polled,poll,tail⟩ := allocated.wait_returns
  cases response with
  | error exception => cases tail
  | ok returned =>
    obtain ⟨rfl,rfl⟩ := tail.ok_returns
    simp only [Option.some.injEq] at poll
    split at poll
    · simp at poll
    · rename_i fresh
      simp only [Prod.mk.injEq,Except.ok.injEq] at poll
      obtain ⟨rfl,rfl⟩ := poll
      obtain ⟨rfl,rfl⟩ := rest.ok_returns
      exact ⟨rfl,rfl,Bool.eq_false_iff.mpr fresh⟩

private theorem filter_map_fixed (cells : List (Nat × String × Term)) (identity : Nat)
    (update : Nat × String × Term → Nat × String × Term)
    (keys : ∀ cell, (update cell).1 = cell.1)
    (fixed : ∀ cell, cell.1 = identity → update cell = cell) :
    (cells.map update).filter (fun cell => cell.1 == identity) =
      cells.filter (fun cell => cell.1 == identity) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    simp only [List.map_cons,List.filter_cons,keys,ih]
    split
    · rename_i same
      rw [fixed cell (by simpa using same)]
    · rfl

private theorem mutex_not_file {mutex : NativeMutex NativeFile} {file : NativeFile}
    {poisoned : Bool} {env : Environment}
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id,NativeMutex.typeName NativeFile,.tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode file])]) :
    NativeFile.lookup ⟨mutex.id⟩ env = none ∧
      NativeFile.directoryHandle ⟨mutex.id⟩ env = none ∧ NativeFile.inode mutex.id env = none := by
  have tag : NativeMutex.typeName NativeFile = "std::sync::Mutex<std::fs::File:borrowed-capability-v1>" := rfl
  simp [NativeFile.lookup,NativeFile.directoryHandle,NativeFile.inode,stored,
    tag,NativeFile.typeName,NativeFile.handleTypeName,
    NativeFile.writableHandleTypeName,NativeFile.directoryTypeName,NativeFile.inodeTypeName]

private theorem shared_store_frame (env : Environment) (target : Nat)
    (file : NativeFile) (handle : NativeFile.Handle) (state : NativeFile.State)
    (differentFile : file.id ≠ target) (differentInode : handle.inode ≠ target) :
    (NativeFile.sharedStore file handle state env).nativeHeap.filter (fun cell => cell.1 == target) =
      env.nativeHeap.filter (fun cell => cell.1 == target) := by
  apply filter_map_fixed
  · intro cell
    repeat' split <;> simp_all
  · intro cell same
    simp [same,Ne.symm differentFile,Ne.symm differentInode]

private theorem retire_frame {mutex : NativeMutex NativeFile} {owned : NativeFile}
    {poisoned : Bool} {env : Environment} (file : NativeFile) (state updated : NativeFile.State)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id,NativeMutex.typeName NativeFile,.tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode owned])])
    (lookup : NativeFile.lookup file env = some state) :
    (NativeFile.retire file updated env).nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      env.nativeHeap.filter (fun cell => cell.1 == mutex.id) := by
  have differentFile : file.id ≠ mutex.id := by
    intro same
    have fileEq : file = ⟨mutex.id⟩ := by cases file; simpa using same
    rw [fileEq,(mutex_not_file stored).1] at lookup
    contradiction
  unfold NativeFile.lookup at lookup
  split at lookup
  · split at lookup
    · rename_i identity tag contents selected
      unfold NativeFile.retire
      simp only [selected]
      split at lookup
      · rename_i regular
        simp only [regular,↓reduceIte]
        apply filter_map_fixed
        · intro cell
          split <;> simp_all
        · intro cell same
          simp [same,Ne.symm differentFile]
      · rename_i notRegular
        simp only [notRegular,Bool.false_eq_true,↓reduceIte]
        split at lookup
        · rename_i shared
          simp only [shared,↓reduceIte]
          unfold NativeFile.sharedLookup at lookup
          cases got : NativeFile.getHandle file tag env with
          | none => simp only [got,Option.bind_eq_bind,Option.bind_none,reduceCtorEq] at lookup
          | some handle =>
            simp only [got,Option.bind_eq_bind,Option.bind_some] at lookup
            cases inode : NativeFile.inode handle.inode env with
            | none => simp [inode] at lookup
            | some image =>
              have differentInode : handle.inode ≠ mutex.id := by
                intro same
                rw [same,(mutex_not_file stored).2.2] at inode
                contradiction
              have decoded : NativeFile.decodeHandle contents = some handle := by
                unfold NativeFile.getHandle at got
                split at got
                · simp at got
                · simpa only [selected,beq_self_eq_true,↓reduceIte] using got
              rw [decoded]
              dsimp only
              rw [filter_map_fixed _ mutex.id _ (by
                intro cell
                split <;> simp_all) (by
                intro cell same
                simp [same,Ne.symm differentFile])]
              exact shared_store_frame env mutex.id file handle updated differentFile differentInode
        · simp at lookup
    · simp at lookup
  · simp at lookup

private theorem close_frame {mutex : NativeMutex NativeFile} {owned : NativeFile}
    {poisoned : Bool} {before after : Environment} (file : NativeFile)
    (stored : before.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id,NativeMutex.typeName NativeFile,.tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode owned])])
    (ready : NativeFile.pollClose file before = some (.ok (),after)) :
    after.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      before.nativeHeap.filter (fun cell => cell.1 == mutex.id) := by
  unfold NativeFile.pollClose at ready
  cases lookup : NativeFile.lookup file before with
  | none =>
    simp only [lookup] at ready
    have differentFile : file.id ≠ mutex.id := by
      intro same
      have fileEq : file = ⟨mutex.id⟩ := by cases file; simpa using same
      rw [fileEq] at ready
      simp [NativeFile.pollDirectoryClose,(mutex_not_file stored).2.1] at ready
    unfold NativeFile.pollDirectoryClose at ready
    cases directory : NativeFile.directoryHandle file before with
    | none => simp [directory] at ready
    | some script =>
      simp only [directory] at ready
      split at ready
      · contradiction
      · cases action : NativeFile.action "close_dir" script with
        | none => simp [action] at ready
        | some choice =>
          obtain ⟨success,error,mask,rest⟩ := choice
          simp only [action] at ready
          change (if mask.size != 0 || (success && error != 0) then
            some ((Except.error .exhausted : Except Exception Unit),before)
            else some (.ok (),NativeFile.storeDirectory file NativeFile.closedDirectoryTypeName rest before)) =
              some (.ok (),after) at ready
          split at ready
          · simp at ready
          · simp only [Option.some.injEq,Prod.mk.injEq] at ready
            obtain ⟨_,rfl⟩ := ready
            apply filter_map_fixed
            · intro cell
              split <;> simp_all
            · intro cell same
              simp [same,Ne.symm differentFile]
  | some state =>
    simp only [lookup] at ready
    split at ready
    · contradiction
    · cases closed : NativeFile.closeStep state with
      | none => simp [closed] at ready
      | some updated =>
        simp only [closed,Option.some.injEq,Prod.mk.injEq] at ready
        obtain ⟨_,rfl⟩ := ready
        exact retire_frame file state updated stored lookup

private theorem close_returns {file : NativeFile} {before after : Environment}
    (trace : Result.ReadyPrefix (NativeFile.close file) before (.ok ()) after) :
    NativeFile.pollClose file before = some (.ok (),after) := by
  simp only [NativeFile.close] at trace
  obtain ⟨response,middle,poll,rest⟩ := trace.wait_returns
  cases response with
  | error exception => cases rest
  | ok returned =>
    obtain ⟨rfl,rfl⟩ := rest.ok_returns
    exact poll

private theorem fields_three (fields : Array Term) (size : fields.size = 3) :
    fields = #[fields[0]'(by omega),fields[1]'(by omega),fields[2]'(by omega)] := by
  apply Array.ext
  · simp [size]
  · intro i before after
    have small : i < 3 := by omega
    have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> rfl

/-- Successful owning cleanup must actually close before removing its mutex. -/
theorem cleanup_complete {mutex : NativeMutex NativeFile} {before after : Environment}
    (trace : Result.ReadyPrefix (NativeMutex.disposeFile mutex) before (.ok ()) after) :
    Cleanup mutex before after := by
  simp only [NativeMutex.disposeFile] at trace
  obtain ⟨contents,middle,read,rest⟩ := trace.bind_returns
  obtain ⟨stored,unchanged⟩ := read_cell_returns read
  subst middle
  cases contents with
  | tuple fields =>
    dsimp only at rest
    split at rest
    · rename_i size
      split at rest
      · rename_i valid
        cases decoded : NativeCodec.decode (α := NativeFile) (fields[2]'(by omega)) with
        | none => simp only [decoded] at rest; cases rest
        | some file =>
          simp only [decoded] at rest
          have conditions : fields[0]'(by omega) = .atom "unlocked" ∧
              (fields[1]'(by omega) = .atom "unpoisoned" ∨ fields[1]'(by omega) = .atom "poisoned") := by
            simpa only [Bool.and_eq_true,Bool.or_eq_true,Term.beq_iff_compare_eq,Term.compare_eq_atom] using valid
          have payload : fields[2]'(by omega) = NativeCodec.encode file := by
            change (match fields[2]'(by omega) with
              | .nativeReference identity => some (⟨identity⟩ : NativeFile)
              | _ => none) = some file at decoded
            split at decoded
            · rename_i identity equal
              simp only [Option.some.injEq] at decoded
              cases decoded
              exact equal
            · contradiction
          have canonical : ∃ poisoned : Bool, fields = #[.atom "unlocked",
              .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode file] := by
            rcases conditions.2 with plain | poisoned
            · exact ⟨false,(fields_three fields size).trans (by simp [conditions.1,plain,payload])⟩
            · exact ⟨true,(fields_three fields size).trans (by simp [conditions.1,poisoned,payload])⟩
          obtain ⟨poisoned,fieldsEq⟩ := canonical
          have canonicalStored : before.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
              [(mutex.id,NativeMutex.typeName NativeFile,.tuple #[.atom "unlocked",
                .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode file])] := by
            simpa only [fieldsEq] using stored
          obtain ⟨returned,closed,closedTrace,tail⟩ := rest.bind_returns
          cases returned
          have poll := close_returns closedTrace
          have retained := (close_frame file canonicalStored poll).trans canonicalStored
          simp only [NativeM.removeCell,Result.wait_bind] at tail
          obtain ⟨response,removed,removePoll,last⟩ := tail.wait_returns
          simp only [retained,beq_self_eq_true,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at removePoll
          obtain ⟨rfl,rfl⟩ := removePoll
          simp only [Result.ok_bind,Result.ofExcept] at last
          obtain ⟨_,sameState⟩ := last.ok_returns
          cases sameState
          exact .close file poisoned before closed canonicalStored poll retained
      · cases rest
    · cases rest
  | _ => cases rest

private theorem finish_returns {mutex : NativeMutex NativeFile} {expected value : Reply}
    {before after : Environment}
    (trace : Result.ReadyPrefix (finish mutex expected) before (.ok value) after) :
    value = expected ∧ Cleanup mutex before after := by
  simp only [finish] at trace
  obtain ⟨returned,middle,cleanup,rest⟩ := trace.bind_returns
  cases returned
  have complete := cleanup_complete cleanup
  simp only [NativeM.ok] at rest
  obtain ⟨values,states⟩ := rest.ok_returns
  subst middle
  exact ⟨values.symm,complete⟩

theorem body_complete {mutex : NativeMutex NativeFile} {before after : Environment} {value : Reply}
    (trace : Result.ReadyPrefix (body mutex) before (.ok value) after) :
    Body mutex before value after := by
  simp only [body] at trace
  obtain ⟨first,middle,readFirst,rest⟩ := trace.bind_returns
  have firstTrace := (GuardedRecovery.LockedCompleteness.locked_iff _ _ _ _ _).mp readFirst
  cases first with
  | Err error =>
    obtain ⟨rfl,cleanup⟩ := finish_returns rest
    exact .firstError error firstTrace cleanup
  | Ok first =>
    obtain ⟨second,readAfter,readSecond,rest⟩ := rest.bind_returns
    have secondTrace := (GuardedRecovery.LockedCompleteness.locked_iff _ _ _ _ _).mp readSecond
    obtain ⟨rfl,cleanup⟩ := finish_returns rest
    exact .second first second firstTrace secondTrace cleanup

private theorem open_returns {path : Str} {before after : Environment}
    {reply : core.result.Result NativeFile NativeIoError}
    (trace : Result.ReadyPrefix (io_core.open_readonly path) before (.ok reply) after) :
    NativeFile.pollOpenReadOnly path before = some (.ok reply,after) := by
  simp only [io_core.open_readonly,monadLift_self,NativeFile.openReadOnly] at trace
  obtain ⟨response,middle,poll,rest⟩ := trace.wait_returns
  cases response with
  | error exception => cases rest
  | ok returned =>
    obtain ⟨rfl,rfl⟩ := rest.ok_returns
    exact poll

/-- Every successful native return of the actual Rust recovery corresponds to
its admitted open, lock/read and owning-cleanup trace, without a valid-state premise. -/
theorem reopen_complete {path : Str} {before after : Environment} {value : Reply}
    (trace : Result.ReadyPrefix (reopen_words path) before (.ok value) after) :
    Reopens path before value after := by
  rw [reopen_contract] at trace
  obtain ⟨opened,middle,openTrace,rest⟩ := trace.bind_returns
  have poll := open_returns openTrace
  cases opened with
  | Err error =>
    obtain ⟨returned,disposed,removed,rest⟩ := rest.bind_returns
    cases returned
    obtain ⟨nonzero,bounded,stored,sameState⟩ :=
      GuardedRecovery.LockedCompleteness.dispose_returns removed
    subst disposed
    simp only [NativeM.ok] at rest
    obtain ⟨values,states⟩ := rest.ok_returns
    cases values
    cases states
    exact .openError error poll nonzero bounded stored
  | Ok file =>
    obtain ⟨mutex,allocated,allocatedTrace,rest⟩ := rest.bind_returns
    obtain ⟨mutexEq,stateEq,fresh⟩ := new_returns allocatedTrace
    subst mutex
    subst allocated
    exact .opened file value poll fresh (body_complete rest)

/-- The original admitted recovery relation and actual extracted recovery have
identical completed local/native value executions, including Rust error values. -/
theorem reopen_iff (path : Str) (before after : Environment) (value : Reply) :
    Result.ReadyPrefix (reopen_words path) before (.ok value) after ↔ Reopens path before value after := by
  constructor
  · exact reopen_complete
  · exact Reopens.ready

end GuardedRecovery.RecoveryCompleteness
