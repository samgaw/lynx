module
public import Record.SharedLogProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.FramedLogProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LockedProperties Record.ResizeProperties

@[expose] def Apart (id : Nat) (frame : List (Nat × String × Term)) : Prop :=
  ∀ cell ∈ frame, cell.1 ≠ id

@[expose] def framedEnv (base : Environment) (counter : Nat)
    (frame : List (Nat × String × Term)) (contents : Term) (state : State) : Environment :=
  {base with refCounter := counter, nativeHeap :=
    frame ++ [(2, NativeFile.typeName, encode state),
    (1, NativeMutex.typeName NativeFile, contents)]}

private theorem filter_apart (id : Nat) (frame : List (Nat × String × Term))
    (apart : Apart id frame) : frame.filter (fun cell => cell.1 == id) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro cell member
  simpa using apart cell member

private theorem map_apart (id : Nat) (value : Nat × String × Term)
    (frame : List (Nat × String × Term)) (apart : Apart id frame) :
    frame.map (fun cell => if cell.1 = id then value else cell) = frame := by
  conv_rhs => rw [← List.map_id frame]
  apply List.map_congr_left
  intro cell member
  simp [apart cell member]

theorem file_lookup (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (state : State) (apart : Apart 2 frame) (bound : 2 ≤ counter) (valid : Valid state) :
    lookup ⟨2⟩ (framedEnv base counter frame contents state) = some state := by
  simp [lookup, framedEnv, filter_apart 2 frame apart, decode_encode state valid, show 1 < counter by omega]

theorem file_store (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (before after : State) (apart : Apart 2 frame) :
    store ⟨2⟩ after (framedEnv base counter frame contents before) = framedEnv base counter frame contents after := by
  simp [store, framedEnv, filter_apart 2 frame apart, map_apart 2 _ frame apart]

theorem no_read_handle (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (state : State) (apart : Apart 2 frame) :
    getHandle ⟨2⟩ handleTypeName (framedEnv base counter frame contents state) = none := by
  simp [getHandle, framedEnv, filter_apart 2 frame apart, typeName, handleTypeName]

theorem seek_poll (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (before after : State) (position : U64)
    (apart : Apart 2 frame) (bound : 2 ≤ counter) (valid : Valid before) (ready : blocked before = false)
    (step : seekStep before (.end_ 0#i64) = some (.Ok position, after)) :
    pollSeek ⟨2⟩ (.end_ 0#i64) (framedEnv base counter frame contents before) =
      some (.ok (.Ok position, ⟨2⟩), framedEnv base counter frame contents after) := by
  simp only [pollSeek, file_lookup base counter frame contents before apart bound valid]
  simp [ready, step, file_store base counter frame contents before after apart]

theorem write_poll (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (before after : State) (value : U16)
    (apart : Apart 2 frame) (bound : 2 ≤ counter) (valid : Valid before) (ready : blocked before = false)
    (step : writeStep before (payload value) = some (.Ok 4#usize, after)) :
    pollWrite ⟨2⟩ (payload value) (framedEnv base counter frame contents before) =
      some (.ok (.Ok 4#usize, ⟨2⟩), framedEnv base counter frame contents after) := by
  simp only [pollWrite, file_lookup base counter frame contents before apart bound valid]
  simp [-getHandle, ready, step, file_store base counter frame contents before after apart,
    no_read_handle base counter frame contents before apart]

theorem sync_poll (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (before after : State)
    (apart : Apart 2 frame) (bound : 2 ≤ counter) (valid : Valid before) (ready : blocked before = false)
    (step : syncStep before = some (.Ok (), after)) :
    pollSync ⟨2⟩ (framedEnv base counter frame contents before) =
      some (.ok (.Ok ()), framedEnv base counter frame contents after) := by
  simp only [pollSync, file_lookup base counter frame contents before apart bound valid]
  simp [ready, step, file_store base counter frame contents before after apart]

@[expose] def free (poisoned : Bool) : Term :=
  .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), .reference 2]

@[expose] def held (base : Environment) (counter : Nat) (poisoned : Bool) : Term :=
  NativeMutex.lockedContents base.currentPid (counter + 1) poisoned (⟨2⟩ : NativeFile)

@[expose] def guard (base : Environment) (counter : Nat) : NativeGuard NativeFile :=
  ⟨⟨1⟩, counter + 1, base.currentPid, ⟨2⟩⟩

theorem lock_poll (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (poisoned : Bool) (state : State) (bound : 2 ≤ counter) (apart : Apart 1 frame)
    (fresh : frame.any (fun cell => cell.1 == counter + 1) = false) :
    NativeMutex.pollLock (⟨1⟩ : NativeMutex NativeFile)
      (framedEnv base counter frame (free poisoned) state) =
      some (.ok (if poisoned then .Err ⟨guard base counter⟩ else .Ok (guard base counter)),
        framedEnv base (counter + 1) frame (held base counter poisoned) state) := by
  have acquired := NativeMutex.pollLock_unlocked (⟨1⟩ : NativeMutex NativeFile) (⟨2⟩ : NativeFile)
    poisoned (framedEnv base counter frame (free poisoned) state)
    (by simp [framedEnv, free, filter_apart 1 frame apart, NativeCodec.encode])
    (by simp [framedEnv, fresh]; omega)
  simpa [framedEnv, held, guard, map_apart 1 _ frame apart] using acquired

/-- A held guard retains its acquisition token when another caller allocates
resource owners and advances the shared reference counter. -/
theorem release_framed (base : Environment) (counter token : Nat)
    (frame : List (Nat × String × Term))
    (poisoned : Bool) (state : State) (apart : Apart 1 frame) :
    NativeGuard.pollRelease (⟨⟨1⟩, token, base.currentPid, ⟨2⟩⟩ : NativeGuard NativeFile)
      (framedEnv base counter frame (NativeMutex.lockedContents base.currentPid token poisoned
        (⟨2⟩ : NativeFile)) state) =
      some (.ok (), framedEnv base counter frame (free poisoned) state) := by
  cases poisoned <;>
    simp [NativeGuard.pollRelease, framedEnv, free,
      filter_apart 1 frame apart, map_apart 1 _ frame apart, NativeMutex.lockedContents,
      NativeCodec.encode, NativeCodec.decode]

theorem release_poll (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (poisoned : Bool) (state : State) (apart : Apart 1 frame) :
    NativeGuard.pollRelease (guard base counter)
      (framedEnv base (counter + 1) frame (held base counter poisoned) state) =
      some (.ok (), framedEnv base (counter + 1) frame (free poisoned) state) := by
  exact release_framed base (counter + 1) (counter + 1) frame poisoned state apart

/-- Resume the actual append body with its original guard, independently of
allocations performed by other callers since acquisition. -/
theorem guarded_prefix (base : Environment) (counter token : Nat)
    (frame : List (Nat × String × Term)) (poisoned : Bool)
    (before sought written committed : State) (value : U16) (position : U64)
    (bound : 2 ≤ counter) (mutexApart : Apart 1 frame) (fileApart : Apart 2 frame)
    (valid0 : Valid before) (valid1 : Valid sought) (valid2 : Valid written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false) (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok 4#usize, written))
    (sync : syncStep written = some (.Ok (), committed)) :
    let heldGuard : NativeGuard NativeFile := ⟨⟨1⟩, token, base.currentPid, ⟨2⟩⟩
    Result.ReadyPrefix (do
      let (reply, file) ← append_record_or_rollback heldGuard.value value
      NativeGuard.release {heldGuard with value := file}
      NativeM.ok reply)
      (framedEnv base counter frame (NativeMutex.lockedContents base.currentPid token poisoned
        (⟨2⟩ : NativeFile)) before) (.ok (.Ok true))
      (framedEnv base counter frame (free poisoned) committed) := by
  dsimp only
  rw [Record.RollbackProperties.append_contract]
  simp only [bind_assoc, NativeFile.seek, Result.wait_bind]
  refine .wait _ _ _ _ _ _ _
    (seek_poll base counter frame _ before sought position fileApart bound valid0 ready0 seek) ?_
  simp only [Result.ok_bind, NativeFile.write, Result.wait_bind]
  refine .wait _ _ _ _ _ _ _
    (write_poll base counter frame _ sought written value fileApart bound valid1 ready1 write) ?_
  simp only [Result.ok_bind, NativeFile.syncAll, Result.wait_bind]
  refine .wait _ _ _ _ _ _ _
    (sync_poll base counter frame _ written committed fileApart bound valid2 ready2 sync) ?_
  simp only [Result.ok_bind, NativeM.ok, NativeGuard.release, Result.wait_bind]
  exact .wait _ _ _ _ _ _ _ (release_framed base counter token frame poisoned committed mutexApart)
    (.refl _ _)

/-- The actual cross-crate critical section preserves every unrelated heap
cell, including Rustler owner tokens and the resource allocation. -/
theorem critical_prefix (base : Environment) (counter : Nat)
    (frame : List (Nat × String × Term)) (poisoned : Bool)
    (before sought written committed : State) (value : U16) (position : U64)
    (bound : 2 ≤ counter) (mutexApart : Apart 1 frame) (fileApart : Apart 2 frame)
    (fresh : frame.any (fun cell => cell.1 == counter + 1) = false)
    (valid0 : Valid before) (valid1 : Valid sought) (valid2 : Valid written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false) (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok 4#usize, written))
    (sync : syncStep written = some (.Ok (), committed)) :
    Result.ReadyPrefix (locked_append_or_rollback ⟨1⟩ value)
      (framedEnv base counter frame (free poisoned) before) (.ok (.Ok true))
      (framedEnv base (counter + 1) frame (free poisoned) committed) := by
  exact Record.SharedLogProperties.full_write _ value (guard base counter)
    (if poisoned then .Err ⟨guard base counter⟩ else .Ok (guard base counter))
    _ _ _ _ _ _ position (lock_poll base counter frame poisoned before bound mutexApart fresh)
    (by cases poisoned <;> rfl)
    (seek_poll base _ frame _ before sought position fileApart (by omega) valid0 ready0 seek)
    (write_poll base _ frame _ sought written value fileApart (by omega) valid1 ready1 write)
    (sync_poll base _ frame _ written committed fileApart (by omega) valid2 ready2 sync)
    (release_poll base counter frame poisoned committed mutexApart)

/-- A framed successful append preserves all previous bytes and commits exactly
the extracted encoder's complete record. The resource registry is unchanged. -/
theorem append_success (base : Environment) (counter : Nat)
    (frame : List (Nat × String × Term)) (poisoned : Bool)
    (data : ByteArray) (value : U16) (position : Nat) (rest : Term)
    (bound : 2 ≤ counter) (mutexApart : Apart 1 frame) (fileApart : Apart 2 frame)
    (fresh : frame.any (fun cell => cell.1 == counter + 1) = false)
    (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) :
    Result.ReadyPrefix (locked_append_or_rollback ⟨1⟩ value)
      (framedEnv base counter frame (free poisoned) (appendInput data position rest))
      (.ok (.Ok true))
      (framedEnv base (counter + 1) frame (free poisoned)
        (appended (appendInput data position rest) value rest)) ∧
    (appended (appendInput data position rest) value rest).visible.data.toList =
      data.data.toList ++ (encoded value).data.toList ∧
    (appended (appendInput data position rest) value rest).durable =
      (appended (appendInput data position rest) value rest).visible := by
  let before := appendInput data position rest
  let afterSeek := sought before data.size data
    (outcome "write" true 4 (zeroMask data) (outcome "sync_all" true 0 ByteArray.empty rest))
  let afterWrite := written afterSeek (payload value) 4 data (outcome "sync_all" true 0 ByteArray.empty rest)
  have sizeBound : data.size ≤ limit := by omega
  have valid0 : Valid before := ⟨sizeBound, Nat.le_refl _, offset⟩
  have valid1 : Valid afterSeek := ⟨sizeBound, Nat.le_refl _, sizeBound⟩
  have persisted : persist afterSeek.durable
      (overwrite afterSeek.visible afterSeek.position (bytes (payload value)) 4) (zeroMask data) = some data :=
    persist_keep_old _ _
  have valid2 := written_valid afterSeek (payload value) 4 (zeroMask data) data
    (outcome "sync_all" true 0 ByteArray.empty rest) valid1
    (by simp [payload, layout]) (by exact fits) persisted
  refine ⟨critical_prefix base counter frame poisoned before afterSeek afterWrite
    (appended before value rest) value
    (U64.ofNatCore data.size (by simp only [limit] at sizeBound; scalar_tac))
    bound mutexApart fileApart fresh valid0 valid1 valid2
    (by simp [before, appendInput, blocked, outcome])
    (by simp [afterSeek, sought, blocked, outcome])
    (by simp [afterWrite, written, blocked, outcome]) ?_ ?_ ?_, append_bytes data value, rfl⟩
  · simpa only [afterSeek, before, appendInput] using seek_end_step before valid0 (zeroMask data) data _
      (action_outcome _ _ _ _ _) (persist_zero data)
  · simpa [afterWrite, count, Usize.ofNatCore, UScalar.ofNat] using write_step afterSeek (payload value)
      4 (zeroMask data) data _ (by simp [payload, layout]) (by simp [payload, layout, limit]) fits
      (action_outcome _ _ _ _ _) persisted
  · simp [syncStep, afterWrite, written, afterSeek, sought, before, appendInput,
      appended, action_outcome]

end Record.FramedLogProperties
