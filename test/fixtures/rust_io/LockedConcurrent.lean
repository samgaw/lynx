module
public import Record.LockedProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.LockedConcurrent
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties Record.LockedProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties

@[expose] def finish (reply : core.result.Result Bool NativeIoError) : Result Term :=
  .ok (match reply with | .Ok true => Term.true | _ => Term.false)

private def postAcquire (value : U16)
    (reply : Except Exception (core.result.Result (NativeGuard NativeFile)
      (NativePoisonError (NativeGuard NativeFile)))) : Result Term :=
  match reply with
  | .error error => .error error
  | .ok acquired => do
      let guard := recoverGuard acquired
      let (reply, file) ← append_record guard.value value
      NativeGuard.release {guard with value := file}
      finish reply

private theorem worker_wait (value : U16) :
    (do let reply ← locked_append ⟨1⟩ value
        finish reply : Result Term) = .wait (NativeMutex.pollLock ⟨1⟩) (postAcquire value) := by
  rw [critical_contract]
  simp only [NativeMutex.lock, Result.wait_bind, bind_assoc]
  congr 1
  funext reply
  cases reply <;> simp [postAcquire, NativeM.ok]

@[expose] def shared (counter : Nat) (contents : Term) (state : State) :
    Nat × List (Nat × String × Term) :=
  (counter, [(2, NativeFile.typeName, encode state), (1, NativeMutex.typeName NativeFile, contents)])

@[expose] def free : Term :=
  .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (⟨2⟩ : NativeFile)]

@[expose] def owned (pid token : Nat) : Term :=
  NativeMutex.lockedContents pid token false (⟨2⟩ : NativeFile)

private theorem seek_poll (before after : State) (position : U64) (counter : Nat) (contents : Term)
    (valid : Valid before) (ready : blocked before = false)
    (step : seekStep before (.end_ 0#i64) = some (.Ok position, after))
    (fresh : 2 ≤ counter) (env : Environment) (count : env.refCounter = counter)
    (heap : env.nativeHeap = (shared counter contents before).2) :
    pollSeek (⟨2⟩ : NativeFile) (.end_ 0#i64) env =
      some (.ok (.Ok position, ⟨2⟩),
        {env with refCounter := counter, nativeHeap := (shared counter contents after).2}) := by
  have found : lookup (⟨2⟩ : NativeFile) env = some before := by
    simp [lookup, heap, shared, decode_encode before valid]
    omega
  simp only [pollSeek, found]
  simp [ready, step, store, heap, shared, ← count]

private theorem write_poll (before after : State) (value : U16) (counter : Nat) (contents : Term)
    (valid : Valid before) (ready : blocked before = false)
    (step : writeStep before (payload value) = some (.Ok 4#usize, after))
    (fresh : 2 ≤ counter) (env : Environment) (count : env.refCounter = counter)
    (heap : env.nativeHeap = (shared counter contents before).2) :
    pollWrite (⟨2⟩ : NativeFile) (payload value) env =
      some (.ok (.Ok 4#usize, ⟨2⟩),
        {env with refCounter := counter, nativeHeap := (shared counter contents after).2}) := by
  have found : lookup (⟨2⟩ : NativeFile) env = some before := by
    simp [lookup, heap, shared, decode_encode before valid]
    omega
  simp only [pollWrite, found]
  simp [ready, step, store, heap, shared, ← count]

private theorem sync_poll (before after : State) (counter : Nat) (contents : Term)
    (valid : Valid before) (ready : blocked before = false)
    (step : syncStep before = some (.Ok (), after))
    (fresh : 2 ≤ counter) (env : Environment) (count : env.refCounter = counter)
    (heap : env.nativeHeap = (shared counter contents before).2) :
    pollSync (⟨2⟩ : NativeFile) env =
      some (.ok (.Ok ()),
        {env with refCounter := counter, nativeHeap := (shared counter contents after).2}) := by
  have found : lookup (⟨2⟩ : NativeFile) env = some before := by
    simp [lookup, heap, shared, decode_encode before valid]
    omega
  simp only [pollSync, found]
  simp [ready, step, store, heap, shared, ← count]

private theorem held_blocked (pid peer token counter : Nat) (state : State)
    (different : pid ≠ peer) (env : Environment) (owner : env.currentPid = peer)
    (heap : env.nativeHeap = (shared counter (owned pid token) state).2) :
    NativeMutex.pollLock (α := NativeFile) ⟨1⟩ env = none := by
  simp [NativeMutex.pollLock, heap, shared, owned, NativeMutex.lockedContents,
    owner, different]

/-- Each actual IO primitive remains a separate wait and excludes peer acquisition. -/
private theorem critical_exclusive (pid peer token counter : Nat) (different : pid ≠ peer)
    (before sought written committed : State) (value : U16) (position : U64) (fresh : 2 ≤ counter)
    (valid0 : Valid before) (valid1 : Valid sought) (valid2 : Valid written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false) (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok 4#usize, written))
    (sync : syncStep written = some (.Ok (), committed)) :
    Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (postAcquire value (.ok (.Ok ⟨⟨1⟩, token, pid, ⟨2⟩⟩)))
      (shared counter (owned pid token) before) Term.true (shared counter free committed) := by
  simp only [postAcquire, recoverGuard]
  rw [append_contract]
  simp only [bind_assoc, NativeFile.seek, Result.wait_bind]
  refine .wait _ _ (.ok (.Ok position, (⟨2⟩ : NativeFile))) _
    (shared counter (owned pid token) sought) _ _ ?_ ?_ ?_
  · intro env _ count heap
    exact seek_poll before sought position counter _ valid0 ready0 seek fresh env count heap
  · intro env owner _ heap
    exact held_blocked pid peer token counter before different env owner heap
  · simp only [Result.ok_bind, NativeFile.write, Result.wait_bind]
    refine .wait _ _ (.ok (.Ok 4#usize, (⟨2⟩ : NativeFile))) _
      (shared counter (owned pid token) written) _ _ ?_ ?_ ?_
    · intro env _ count heap
      exact write_poll sought written value counter _ valid1 ready1 write fresh env count heap
    · intro env owner _ heap
      exact held_blocked pid peer token counter sought different env owner heap
    · simp only [Result.ok_bind, NativeFile.syncAll, Result.wait_bind]
      refine .wait _ _ (.ok (.Ok ())) _
        (shared counter (owned pid token) committed) _ _ ?_ ?_ ?_
      · intro env _ count heap
        exact sync_poll written committed counter _ valid2 ready2 sync fresh env count heap
      · intro env owner _ heap
        exact held_blocked pid peer token counter written different env owner heap
      · simp only [Result.ok_bind, NativeM.ok, NativeGuard.release, Result.wait_bind]
        refine .wait _ _ (.ok ()) _ (shared counter free committed) _ _ ?_ ?_ ?_
        · intro env owner count heap
          simp [NativeGuard.pollRelease, heap, shared, owned, free,
            NativeMutex.lockedContents, NativeCodec.encode, NativeCodec.decode, owner, count]
        · intro env owner _ heap
          exact held_blocked pid peer token counter committed different env owner heap
        · exact .done Term.true _

private theorem append_exclusive (pid peer token counter : Nat) (different : pid ≠ peer) (fresh : 2 ≤ counter)
    (data : ByteArray) (value : U16) (position : Nat) (rest : Term)
    (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) :
    Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (postAcquire value (.ok (.Ok ⟨⟨1⟩, token, pid, ⟨2⟩⟩)))
      (shared counter (owned pid token) (appendInput data position rest)) Term.true
      (shared counter free (appended (appendInput data position rest) value rest)) := by
  let before := appendInput data position rest
  let afterSeek := sought before data.size data
    (outcome "write" true 4 (zeroMask data) (outcome "sync_all" true 0 ByteArray.empty rest))
  let afterWrite := written afterSeek (payload value) 4 data (outcome "sync_all" true 0 ByteArray.empty rest)
  have bound : data.size ≤ limit := by omega
  have valid0 : Valid before := ⟨bound, Nat.le_refl _, offset⟩
  have valid1 : Valid afterSeek := ⟨bound, Nat.le_refl _, bound⟩
  have accepted : persist afterSeek.durable
      (overwrite afterSeek.visible afterSeek.position (bytes (payload value)) 4) (zeroMask data) = some data := by
    exact persist_keep_old _ _
  have valid2 := written_valid afterSeek (payload value) 4 (zeroMask data) data
    (outcome "sync_all" true 0 ByteArray.empty rest) valid1
    (by simp [payload, layout]) fits accepted
  refine critical_exclusive pid peer token counter different before afterSeek afterWrite (appended before value rest) value
    (U64.ofNatCore data.size (by simp only [limit] at bound; scalar_tac)) fresh valid0 valid1 valid2
    (by simp [before, appendInput, blocked, outcome])
    (by simp [afterSeek, sought, blocked, outcome])
    (by simp [afterWrite, written, blocked, outcome]) ?_ ?_ ?_
  · simpa only [afterSeek, before, appendInput] using seek_end_step before valid0 (zeroMask data) data _
      (action_outcome _ _ _ _ _) (persist_zero data)
  · simpa [afterWrite, count, Usize.ofNatCore, UScalar.ofNat] using write_step afterSeek (payload value) 4 (zeroMask data) data _
      (by simp [payload, layout]) (by simp [payload, layout, limit]) fits
      (action_outcome _ _ _ _ _) accepted
  · simp [syncStep, afterWrite, written, afterSeek, sought, before, appendInput,
      appended, action_outcome]

private theorem append_trace (pid token counter : Nat) (fresh : 2 ≤ counter)
    (data : ByteArray) (value : U16) (position : Nat) (rest : Term)
    (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) :
    Result.SharedSteps pid (postAcquire value (.ok (.Ok ⟨⟨1⟩, token, pid, ⟨2⟩⟩)))
      (shared counter (owned pid token) (appendInput data position rest)) Term.true
      (shared counter free (appended (appendInput data position rest) value rest)) :=
  (append_exclusive pid (pid + 1) token counter (by omega) fresh data value position rest fits offset).ready

@[expose] def extended (data : ByteArray) (value : U16) : ByteArray :=
  overwrite data data.size (bytes (payload value)) 4

private theorem extended_size (data : ByteArray) (value : U16) :
    (extended data value).size = data.size + 4 := by
  have size := overwrite_size data (bytes (payload value)) data.size 4 (by simp [bytes_size, payload, layout])
  simpa [extended, bytes_size, payload, layout] using size

/-- Two actual Rust append callers contend for one mutex and retain both
synchronized records. Every seek, write, sync and release remains a scheduler
boundary. The schedule attempts the child while the root holds the guard. -/
theorem appends_interleave (data : ByteArray) (first second : U16) (position : Nat) (rest : Term)
    (fits : data.size + 8 ≤ limit) (offset : position ≤ limit) :
    let next := appendInput (extended data first) (data.size + 4) rest
    let before := appendInput data position next.script
    let after := appended next second rest
    let worker := fun value : U16 => (do
      let reply ← locked_append ⟨1⟩ value
      finish reply : Result Term)
    let computation : Result Term := do
      let _ ← Result.schedule (worker second) .ok
      worker first
    computation { refCounter := 2
                  nativeHeap := (shared 2 free before).2
                  schedule := [.current, .swap 2] } =
      (.ok Term.true, {pidCounter := 2, refCounter := 4, nativeHeap := (shared 4 free after).2}) ∧
    after.visible.data.toList = data.data.toList ++ (encoded first).data.toList ++ (encoded second).data.toList := by
  dsimp only
  let next := appendInput (extended data first) (data.size + 4) rest
  let before := appendInput data position next.script
  let middle := appended before first next.script
  let after := appended next second rest
  have firstFits : data.size + 4 ≤ limit := by omega
  have secondFits : (extended data first).size + 4 ≤ limit := by rw [extended_size]; omega
  have firstTrace := append_trace 1 3 3 (by decide) data first position next.script firstFits offset
  have secondTrace := append_trace 2 4 4 (by decide) (extended data first) second (data.size + 4) rest secondFits (by omega)
  have middleNext : middle = next := rfl
  have trace := Result.two_wait_interleave_steps
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire first)
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire second)
    (.ok (.Ok ⟨⟨1⟩, 3, 1, ⟨2⟩⟩)) (.ok (.Ok ⟨⟨1⟩, 4, 2, ⟨2⟩⟩)) Term.true Term.true
    (shared 2 free before) (shared 3 (owned 1 3) before) (shared 3 free middle)
    (shared 4 (owned 2 4) middle) (shared 4 free after)
    (by simp [NativeMutex.pollLock, shared, free, owned, NativeMutex.lockedContents,
      NativeCodec.encode, NativeCodec.decode])
    firstTrace
    (by simp [NativeMutex.pollLock, shared, owned, NativeMutex.lockedContents])
    (by simp [NativeMutex.pollLock, shared, free, owned, NativeMutex.lockedContents,
      NativeCodec.encode, NativeCodec.decode])
    (by simpa only [middleNext] using secondTrace)
  constructor
  · simpa only [worker_wait, Result.schedule_bind, Result.ok_bind, shared, before, next, after] using trace
  · have bytes := append_bytes (extended data first) second
    have earlier := append_bytes data first
    simpa only [after, next, appended, appendInput, extended, earlier] using bytes

private theorem lock_poll (pid counter : Nat) (state : State) (fresh : 2 ≤ counter)
    (env : Environment) (owner : env.currentPid = pid) (count : env.refCounter = counter)
    (heap : env.nativeHeap = (shared counter free state).2) :
    NativeMutex.pollLock (α := NativeFile) ⟨1⟩ env =
      some (.ok (.Ok ⟨⟨1⟩, counter + 1, pid, ⟨2⟩⟩),
        {env with
          refCounter := counter + 1
          nativeHeap := (shared (counter + 1) (owned pid (counter + 1)) state).2}) := by
  simp [NativeMutex.pollLock, heap, shared, free, owned, NativeMutex.lockedContents,
    NativeCodec.encode, NativeCodec.decode, count, owner]
  omega

private theorem full_append_trace (pid : Nat) (data : ByteArray) (value : U16)
    (position : Nat) (rest : Term) (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) :
    Result.SharedSteps pid (.wait (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire value))
      (shared 3 free (appendInput data position rest)) Term.true
      (shared 4 free (appended (appendInput data position rest) value rest)) := by
  refine .wait _ _ (.ok (.Ok (⟨⟨1⟩, 4, pid, ⟨2⟩⟩ : NativeGuard NativeFile))) _
    (shared 4 (owned pid 4) (appendInput data position rest)) _ _ ?_
    (append_trace pid 4 4 (by decide) data value position rest fits offset)
  intro env owner count heap
  exact lock_poll pid 3 _ (by decide) env owner count heap

/-- Under every finite scheduler choice list, the actual two Rust callers
produce one of the two serial append images. Both images retain the original
prefix and both synchronized encodings; a return after release is not a write. -/
theorem appends_all_schedules (data : ByteArray) (first second : U16) (position : Nat) (rest : Term)
    (fits : data.size + 8 ≤ limit) (offset : position ≤ limit) (choices : List ScheduleChoice) :
    let nextFirst := appendInput (extended data first) (data.size + 4) rest
    let nextSecond := appendInput (extended data second) (data.size + 4) rest
    let before := appendInput data position nextFirst.script
    let worker := fun value : U16 => (do
      let reply ← locked_append ⟨1⟩ value
      finish reply : Result Term)
    let observed := (do
      let _ ← Result.schedule (worker second) .ok
      worker first : Result Term)
      {refCounter := 2, nativeHeap := (shared 2 free before).2, schedule := choices}
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
        (.ok Term.true, shared 4 free (appended nextFirst second rest)) ∨
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
        (.ok Term.true, shared 4 free (appended nextSecond first rest)) := by
  dsimp only
  let nextFirst := appendInput (extended data first) (data.size + 4) rest
  let nextSecond := appendInput (extended data second) (data.size + 4) rest
  let before := appendInput data position nextFirst.script
  let middleRoot := appended before first nextFirst.script
  let middleChild := appended before second nextFirst.script
  have firstFits : data.size + 4 ≤ limit := by omega
  have secondFits (value : U16) : (extended data value).size + 4 ≤ limit := by rw [extended_size]; omega
  have scripts : nextFirst.script = nextSecond.script := by
    simp [nextFirst, nextSecond, appendInput, zeroMask, extended_size]
  have rootNext : middleRoot = nextFirst := rfl
  have childNext : middleChild = nextSecond := by
    simpa only [middleChild, appended, before, appendInput, nextSecond, extended] using
      congrArg (fun script => (State.mk (extended data second) (extended data second) (data.size + 4) script)) scripts
  have rootExclusive := append_exclusive 1 2 3 3 (by decide) (by decide)
    data first position nextFirst.script firstFits offset
  have childExclusive := append_exclusive 2 1 3 3 (by decide) (by decide)
    data second position nextFirst.script firstFits offset
  have childAfter := full_append_trace 2 (extended data first) second (data.size + 4) rest (secondFits first) (by omega)
  have rootAfter := full_append_trace 1 (extended data second) first (data.size + 4) rest (secondFits second) (by omega)
  have result := Result.two_wait_serial_orders
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire first)
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire second)
    (.ok (.Ok ⟨⟨1⟩, 3, 1, ⟨2⟩⟩)) (.ok (.Ok ⟨⟨1⟩, 3, 2, ⟨2⟩⟩)) Term.true Term.true
    (shared 2 free before) (shared 3 (owned 1 3) before) (shared 3 free middleRoot)
    (shared 4 free (appended nextFirst second rest))
    (shared 3 (owned 2 3) before) (shared 3 free middleChild)
    (shared 4 free (appended nextSecond first rest))
    (lock_poll 1 2 before (by decide)) (lock_poll 2 2 before (by decide))
    rootExclusive (by simpa only [rootNext] using childAfter)
    childExclusive (by simpa only [childNext] using rootAfter) choices
  simpa only [worker_wait, Result.schedule_bind, Result.ok_bind, shared,
    before, nextFirst, nextSecond] using result

end Record.LockedConcurrent
