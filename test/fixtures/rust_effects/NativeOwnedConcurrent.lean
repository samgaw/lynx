module
public import Owned.Critical
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Owned.ResourceConcurrent
open Owned.Critical

attribute [local simp] NativeCodec.typeName NativeMutex.typeName
  NativeResourceArc.typeName NativeResourceArc.handleType NativeResourceArc.termType

@[expose] def payload (amount : U64) : ScalarResource := ⟨⟨amount⟩⟩
@[expose] def pin (amount : U64) := NativeResourceArc.vmCells (payload amount) 2 4 5
@[expose] def both (amount : U64) : List (Nat × String × Term) :=
  (7,NativeResourceArc.handleType ScalarResource,.nativeReference 2) ::
  (6,NativeResourceArc.handleType ScalarResource,.nativeReference 2) ::
    (pin amount).map fun cell => if cell.1 == 2 then
      (2,NativeResourceArc.typeName ScalarResource,.tuple #[.integer 3,NativeCodec.encode (payload amount)]) else cell
@[expose] def retained (parent : Bool) (amount : U64) :=
  ((both amount).filter fun cell => cell.1 != (if parent then 7 else 6)).map fun cell =>
    if cell.1 == 2 then
      (2,NativeResourceArc.typeName ScalarResource,.tuple #[.integer 2,NativeCodec.encode (payload amount)]) else cell
@[expose] def initialFrame (first parent : Bool) (amount : U64) :=
  if first then both amount else retained parent amount
@[expose] def finalFrame (first parent : Bool) (amount : U64) :=
  if first then retained (!parent) amount else pin amount
@[expose] def owner (parent : Bool) : NativeResourceArc ScalarResource := ⟨2,if parent then 6 else 7⟩
@[expose] def count (first : Bool) : Nat := if first then 3 else 2
@[expose] def free (value : U64) : Term :=
  .tuple #[.atom "unlocked",.atom "unpoisoned",NativeCodec.encode (effects_core.Counter.mk value)]
@[expose] def held (pid : PID) (token : Nat) (value : U64) : Term :=
  NativeMutex.lockedContents pid token false (effects_core.Counter.mk value)
@[expose] def shared (refs : Nat) (frame : List (Nat × String × Term)) (contents : Term) :
    Nat × List (Nat × String × Term) :=
  (refs,frame ++ [(1,NativeMutex.typeName effects_core.Counter,contents)])

private theorem increment_expected (before amount after : U64)
    (sum : after.val = before.val + amount.val) :
    effects_core.increment ⟨before⟩ amount = Result.ok (true,⟨after⟩) := by
  obtain ⟨changed,updated,returned,property⟩ := increment_spec ⟨before⟩ amount
  cases changed with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte] at property
    have bound : after.val ≤ U64.max := by scalar_tac
    omega
  | true =>
    simp only [↓reduceIte] at property
    have same : updated = effects_core.Counter.mk after := by
      cases updated with
      | mk value => exact congrArg effects_core.Counter.mk (UScalar.eq_of_val_eq (property.trans sum.symm))
    simpa [same] using returned

abbrev Acquired := Except Exception
  (core.result.Result (NativeGuard effects_core.Counter) (NativePoisonError (NativeGuard effects_core.Counter)))

@[expose] def postAcquire (resource : NativeResourceArc ScalarResource) (reply : Acquired) : Result Term :=
  match reply with
  | .error error => .error error
  | .ok acquired => do
    let guard ← effects_core.recover_guard acquired
    let data ← NativeResourceArc.deref resource
    NativeOwnedDrop.drop resource
    let (changed,updated) ← effects_core.increment guard.value data.counter.value
    NativeGuard.release {guard with value := updated}
    Result.ok (if changed then Term.true else Term.false)

/-- The continuation is the actual cross-crate Rust body, including the resource
read and consuming drop before the guard's checked update and release. -/
theorem worker_wait (resource : NativeResourceArc ScalarResource) :
    (do let changed ← locked_increment_from_resource ⟨1⟩ resource
        Result.ok (if changed then Term.true else Term.false)) =
      .wait (NativeMutex.pollLock ⟨1⟩) (postAcquire resource) := by
  simp only [locked_increment_from_resource,scalar_resource_read,effects_core.counter_value,
    release_contract,monadLift_self,NativeM.ok,bind_assoc,NativeMutex.lock,Result.wait_bind]
  congr 1
  funext reply
  cases reply <;> simp [postAcquire]

private theorem blocked (pid peer : PID) (token refs : Nat) (different : pid ≠ peer)
    (first parent : Bool) (before amount : U64) (env : Environment)
    (actor : env.currentPid = peer)
    (heap : env.nativeHeap = (shared refs (initialFrame first parent amount) (held pid token before)).2) :
    NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩ env = none := by
  cases first <;> cases parent <;>
    simp [NativeMutex.pollLock,heap,shared,initialFrame,both,retained,pin,
      NativeResourceArc.vmCells,List.filter,List.map,held,NativeMutex.lockedContents,NativeCodec.roundtrip,actor,different]

private theorem final_blocked (pid peer : PID) (token refs : Nat) (different : pid ≠ peer)
    (first parent : Bool) (before amount : U64) (env : Environment)
    (actor : env.currentPid = peer)
    (heap : env.nativeHeap = (shared refs (finalFrame first parent amount) (held pid token before)).2) :
    NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩ env = none := by
  cases first <;> cases parent <;>
    simp [NativeMutex.pollLock,heap,shared,finalFrame,both,retained,pin,
      NativeResourceArc.vmCells,List.filter,List.map,held,NativeMutex.lockedContents,NativeCodec.roundtrip,actor,different]

/-- Resource lookup and owner-release get/set nodes stay inside the actual held
mutex. Every local state excludes the peer, not only the IO wait boundaries. -/
theorem body_exclusive (pid peer : PID) (token refs : Nat) (different : pid ≠ peer)
    (first parent : Bool) (before amount after : U64)
    (sum : after.val = before.val + amount.val) :
    Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩)
      (postAcquire (owner parent) (.ok (.Ok ⟨⟨1⟩,token,pid,⟨before⟩⟩)))
      (shared refs (initialFrame first parent amount) (held pid token before)) Term.true
      (shared refs (finalFrame first parent amount) (free after)) := by
  simp only [postAcquire,effects_core.recover_guard,NativeM.ok]
  apply NativeResourceArc.deref_live_exclusiveSteps pid peer _ (owner parent) (payload amount) (count first)
  · cases first <;> decide
  · cases first <;> decide
  · cases first <;> cases parent <;>
      simp [shared,owner,initialFrame,both,retained,pin,NativeResourceArc.vmCells,List.filter,List.map]
  · cases first <;> cases parent <;>
      simp [shared,owner,initialFrame,count,both,retained,pin,NativeResourceArc.vmCells,List.filter,List.map]
  · cases first <;> cases parent <;>
      simp [shared,owner,initialFrame,count,both,retained,pin,NativeResourceArc.vmCells,List.filter,List.map]
  · intro env actor _ heap
    exact blocked pid peer token refs different first parent before amount env actor heap
  · simp only [payload,NativeOwnedDrop.drop]
    have consumed := NativeResourceArc.releaseOwned_live_exclusiveSteps pid peer
      (NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩) (owner parent) (payload amount) (count first)
      (shared refs (initialFrame first parent amount) (held pid token before))
      (shared refs (finalFrame first parent amount) (free after))
      (fun _ => do
        let (changed,updated) ← effects_core.increment ⟨before⟩ amount
        NativeGuard.release (⟨⟨1⟩,token,pid,updated⟩ : NativeGuard effects_core.Counter)
        Result.ok (if changed then Term.true else Term.false)) Term.true
      (by cases first <;> decide) (by cases first <;> decide)
      (by cases first <;> cases parent <;> simp [shared,owner,initialFrame,both,retained,pin,NativeResourceArc.vmCells,List.filter,List.map])
      (by cases first <;> cases parent <;> simp [shared,owner,initialFrame,count,both,retained,pin,NativeResourceArc.vmCells,List.filter,List.map])
      (by cases first <;> cases parent <;> simp [shared,owner,initialFrame,count,both,retained,pin,NativeResourceArc.vmCells,List.filter,List.map])
      (by intro env actor _ heap; exact blocked pid peer token refs different first parent before amount env actor heap) ?_
    · exact consumed
    · have updated := increment_expected before amount after sum
      simp only [updated,Result.ok_bind,NativeGuard.release,Result.wait_bind,↓reduceIte]
      have releaseTrace : Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩)
          (NativeGuard.release (⟨⟨1⟩,token,pid,⟨after⟩⟩ : NativeGuard effects_core.Counter) >>= fun _ => Result.ok Term.true)
          (shared refs (finalFrame first parent amount) (held pid token before)) Term.true
          (shared refs (finalFrame first parent amount) (free after)) := by
        simp only [NativeGuard.release,Result.wait_bind]
        refine .wait _ _ (.ok ()) _ _ _ _ ?_ ?_ (.done _ _)
        · intro env actor counter heap
          cases first <;> cases parent <;>
            simp [NativeGuard.pollRelease,heap,actor,counter,shared,finalFrame,both,retained,pin,
              NativeResourceArc.vmCells,List.filter,List.map,held,free,NativeMutex.lockedContents,NativeCodec.roundtrip]
        · intro env actor _ heap
          exact final_blocked pid peer token refs different first parent before amount env actor heap
      cases first <;> cases parent <;>
        simpa [NativeGuard.release,Result.wait_bind,shared,initialFrame,finalFrame,owner,count,
          both,retained,pin,NativeResourceArc.vmCells,List.filter,List.map] using releaseTrace


private theorem acquire_ready (pid : PID) (refs : Nat) (first parent : Bool)
    (before amount : U64) (fresh : 7 ≤ refs) (env : Environment)
    (actor : env.currentPid = pid) (counter : env.nativeRefCounter = refs)
    (heap : env.nativeHeap = (shared refs (initialFrame first parent amount) (free before)).2) :
    NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩ env =
      some (.ok (.Ok ⟨⟨1⟩,refs + 1,pid,⟨before⟩⟩),
        {env with
          nativeRefCounter := refs + 1,
          nativeHeap := (shared (refs + 1) (initialFrame first parent amount) (held pid (refs + 1) before)).2}) := by
  have acquired := NativeMutex.pollLock_unlocked (⟨1⟩ : NativeMutex effects_core.Counter)
    (effects_core.Counter.mk before) false env
    (by cases first <;> cases parent <;>
        simp [heap,shared,initialFrame,both,retained,pin,NativeResourceArc.vmCells,List.filter,List.map,free])
    (by cases first <;> cases parent <;>
        simp [heap,counter,shared,initialFrame,both,retained,pin,NativeResourceArc.vmCells,List.filter,List.map]
        all_goals omega)
  cases first <;> cases parent <;>
    simpa [heap,counter,actor,shared,initialFrame,both,retained,pin,NativeResourceArc.vmCells,List.filter,List.map,held] using acquired

private theorem second_steps (pid peer : PID) (parent : Bool) (refs : Nat)
    (different : pid ≠ peer) (fresh : 7 ≤ refs) (before amount after : U64)
    (sum : after.val = before.val + amount.val) :
    Result.SharedSteps pid
      (.wait (NativeMutex.pollLock ⟨1⟩) (postAcquire (owner parent)))
      (shared refs (retained parent amount) (free before)) Term.true
      (shared (refs + 1) (pin amount) (free after)) := by
  refine .wait _ _ (.ok (.Ok (⟨⟨1⟩,refs + 1,pid,⟨before⟩⟩ : NativeGuard effects_core.Counter))) _
    (shared (refs + 1) (retained parent amount) (held pid (refs + 1) before)) _ _ ?_ ?_
  · intro env actor counter heap
    exact acquire_ready pid refs false parent before amount fresh env actor counter heap
  · simpa only [initialFrame,finalFrame,Bool.false_eq_true,↓reduceIte] using
      (body_exclusive pid peer (refs + 1) (refs + 1) different false parent before amount after sum).ready

/-- Every finite scheduler choice list serializes both actual Rust callers.
Both temporary owners are consumed under the mutex and one VM pin survives;
no scheduler bound, fixed acquisition order or fairness assumption is used. -/
theorem updates_all_choices (before amount intermediate final : U64)
    (firstSum : intermediate.val = before.val + amount.val)
    (secondSum : final.val = intermediate.val + amount.val) (choices : List ScheduleChoice) :
    let worker := fun resource : NativeResourceArc ScalarResource => (do
      let changed ← locked_increment_from_resource ⟨1⟩ resource
      Result.ok (if changed then Term.true else Term.false))
    let observed := (Result.schedule {} (worker (owner false)) (fun _ => worker (owner true))).run
      {nativeRefCounter := 7,nativeHeap := (shared 7 (both amount) (free before)).2} choices
    (observed.1,observed.2.nativeRefCounter,observed.2.nativeHeap) =
      (.ok Term.true,shared 9 (pin amount) (free final)) := by
  dsimp only
  simp only [worker_wait]
  have serialized := Result.two_wait_serial_orders
    (NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩) (postAcquire (owner true))
    (NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩) (postAcquire (owner false))
    (.ok (.Ok ⟨⟨1⟩,8,[],⟨before⟩⟩)) (.ok (.Ok ⟨⟨1⟩,8,[1],⟨before⟩⟩))
    Term.true Term.true Term.true Term.true
    (shared 7 (both amount) (free before))
    (shared 8 (both amount) (held [] 8 before))
    (shared 8 (retained false amount) (free intermediate)) (shared 9 (pin amount) (free final))
    (shared 8 (both amount) (held [1] 8 before))
    (shared 8 (retained true amount) (free intermediate)) (shared 9 (pin amount) (free final))
    (by intro env actor counter heap; exact acquire_ready [] 7 true true before amount (by decide) env actor counter heap)
    (by intro env actor counter heap; exact acquire_ready [1] 7 true false before amount (by decide) env actor counter heap)
    (by simpa only [initialFrame,finalFrame,Bool.true_eq,↓reduceIte,Bool.not_true] using
      body_exclusive [] [1] 8 8 (by decide) true true before amount intermediate firstSum)
    (second_steps [1] [] false 8 (by decide) (by decide) intermediate amount final secondSum)
    (by simpa only [initialFrame,finalFrame,Bool.true_eq,↓reduceIte,Bool.not_false] using
      body_exclusive [1] [] 8 8 (by decide) true false before amount intermediate firstSum)
    (second_steps [] [1] true 8 (by decide) (by decide) intermediate amount final secondSum) choices
  exact serialized.elim id id

end Owned.ResourceConcurrent
