module
public import Record.LockedPrefixInvariant
public import Record.RepairingLogProperties
public import Record.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.GuardedRepairAdapter
open NativeFile Record.Properties Record.ResizeProperties Record.LogProperties Record.RepairCrashProperties Record.CrashProperties

/-- Logical allocation admission for a pinned resource at a call boundary.
The error capability may already have been consumed by an earlier call. -/
class Admission where
  counter : Nat
  bound : 6 ≤ counter
  errorAvailable : Bool

instance initialAdmission : Admission := ⟨6,by decide,true⟩

variable [admission : Admission]

local instance ownerLayout : HeapLayout := HeapLayout.ownerFirst (admission.counter + 1)

@[simp] private theorem small_le_counter (id : Nat) (small : id ≤ 6) : id ≤ admission.counter :=
  small.trans admission.bound
@[simp] private theorem small_ne_owner (id : Nat) (small : id ≤ 6) : id ≠ admission.counter + 1 := by
  have := admission.bound; omega
@[simp] private theorem owner_ne_small (id : Nat) (small : id ≤ 6) : admission.counter + 1 ≠ id :=
  (small_ne_owner id small).symm
@[simp] private theorem small_ne_lease (id : Nat) (small : id ≤ 6) : id ≠ admission.counter + 2 := by
  have := admission.bound; omega
@[simp] private theorem owner_ne_lease : admission.counter + 1 ≠ admission.counter + 2 := by omega
@[simp] private theorem counter_ne_small (id : Nat) (small : id < 6) : admission.counter ≠ id := by
  have := admission.bound; omega
@[simp] private theorem small_ne_counter (id : Nat) (small : id < 6) : id ≠ admission.counter :=
  (counter_ne_small id small).symm
@[simp] private theorem counter_not_lt_small (id : Nat) (small : id ≤ 6) : ¬admission.counter < id := by
  have := admission.bound; omega
@[simp] private theorem owner_not_lt_small (id : Nat) (small : id ≤ 6) : ¬admission.counter + 1 < id := by
  have := admission.bound; omega
@[simp] private theorem lease_not_lt_small (id : Nat) (small : id ≤ 6) : ¬admission.counter + 2 < id := by
  have := admission.bound; omega
@[simp] private theorem small_beq_owner (id : Nat) (small : id ≤ 6) : (id == admission.counter + 1) = false :=
  Bool.eq_false_iff.mpr (fun equal => small_ne_owner id small (_root_.beq_iff_eq.mp equal))
@[simp] private theorem owner_beq_small (id : Nat) (small : id ≤ 6) : (admission.counter + 1 == id) = false :=
  Bool.eq_false_iff.mpr (fun equal => owner_ne_small id small (_root_.beq_iff_eq.mp equal))
@[simp] private theorem counter_beq_small (id : Nat) (small : id < 6) : (admission.counter == id) = false :=
  Bool.eq_false_iff.mpr (fun equal => counter_ne_small id small (_root_.beq_iff_eq.mp equal))
@[simp] private theorem small_beq_counter (id : Nat) (small : id < 6) : (id == admission.counter) = false :=
  Bool.eq_false_iff.mpr (fun equal => small_ne_counter id small (_root_.beq_iff_eq.mp equal))
@[simp] private theorem counter_bne_small (id : Nat) (small : id < 6) : (admission.counter != id) = true := by
  simp only [bne,counter_beq_small id small,Bool.not_false]
@[simp] private theorem max_counter : max admission.counter 2 = admission.counter :=
  Nat.max_eq_left (small_le_counter 2 (by decide))
@[simp] private theorem max_owner : max (admission.counter + 1) 2 = admission.counter + 1 := by
  apply Nat.max_eq_left; have := admission.bound; omega
@[simp] private theorem max_lease : max (admission.counter + 2) 2 = admission.counter + 2 := by
  apply Nat.max_eq_left; have := admission.bound; omega

@[expose] def payload : shared_log.LogResource := ⟨⟨1⟩⟩
@[expose] def pinCells : List (Nat × String × Term) := [
  (5,NativeResourceArc.handleType shared_log.LogResource,.nativeReference 3),
  (6,NativeResourceArc.termType shared_log.LogResource,.tuple #[.nativeReference 3,.nativeReference 5])]
@[expose] def errorCell : Nat × String × Term := (4,NativeIoError.typeName,.atom "live")
@[expose] def pinnedFrame : List (Nat × String × Term) := NativeResourceArc.vmCells payload 3 5 6 ++ (if admission.errorAvailable then [errorCell] else [])
@[expose] def decodedFrame : List (Nat × String × Term) :=
  (admission.counter + 1,NativeResourceArc.handleType shared_log.LogResource,.nativeReference 3) :: pinnedFrame.map (fun cell =>
    if cell.1 = 3 then (3,NativeResourceArc.typeName shared_log.LogResource,
      .tuple #[.integer 2,NativeCodec.encode payload]) else cell)
@[expose] def pinned (base : Environment) (poisoned : Bool) (state : State) : Environment :=
  Record.LockedPrefixInvariant.view base admission.counter pinnedFrame (Record.LockedPrefixInvariant.free poisoned) state
@[expose] def decoded (base : Environment) (poisoned : Bool) (state : State) : Environment :=
  Record.LockedPrefixInvariant.view base (admission.counter + 1) decodedFrame (Record.LockedPrefixInvariant.free poisoned) state
@[expose] def returned (base : Environment) (poisoned consumed : Bool) (state : State) : Environment :=
  Record.LockedPrefixInvariant.view base (admission.counter + 2)
    (if consumed then NativeResourceArc.vmCells payload 3 5 6 else pinnedFrame)
    (Record.LockedPrefixInvariant.free poisoned) state

/-- The known byte prefix and independent VM pin survive every adapter phase.
Owner counts and exact release state are established separately on returns. -/
@[expose] def Safe (values : List U16) (world : Environment) : Prop :=
  ∃ state, lookup ⟨2⟩ world = some state ∧ Admitted state ∧
    Prefix (disk (logBytes values)) state.visible ∧ Prefix (disk (logBytes values)) state.durable ∧
    ∀ cell ∈ pinCells, cell ∈ world.nativeHeap

private theorem safe_view (base : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (state : State) (values : List U16) (apart : Separate (⟨2⟩ : NativeFile) frame)
    (pins : ∀ cell ∈ pinCells, cell ∈ frame) (valid : Admitted state)
    (visible : Prefix (disk (logBytes values)) state.visible) (durable : Prefix (disk (logBytes values)) state.durable) :
    Safe values (Record.LockedPrefixInvariant.view base counter frame contents state) := by
  refine ⟨state,lookup_admitted _ _ _ _ ?_ valid,valid,visible,durable,?_⟩
  · simp [Separate] at apart ⊢; exact apart
  · intro cell member
    simp only [Record.LockedPrefixInvariant.view,fileEnv,HeapLayout.mem_arrange,List.mem_cons]
    exact .inr (.inr (pins cell member))

private theorem decoded_pins : ∀ cell ∈ pinCells, cell ∈ decodedFrame := by
  intro cell member
  simp only [pinCells,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> simp [decodedFrame,pinnedFrame,NativeResourceArc.vmCells]

private theorem pinned_proof (base : Environment) (poisoned : Bool) (state : State) :
    NativeResourceArc.Pinned payload 3 5 6 (pinned base poisoned state) := by
  constructor
  · simp [pinned,Record.LockedPrefixInvariant.view,fileEnv]
  · intro cell member
    have small : ∀ cell ∈ ((2,NativeFile.typeName,NativeFile.encode state) ::
        (1,NativeMutex.typeName NativeFile,Record.LockedPrefixInvariant.free poisoned) :: pinnedFrame),
        cell.1 ≤ admission.counter := by
      cases live : admission.errorAvailable <;>
        simp [pinnedFrame,NativeResourceArc.vmCells,errorCell,live]
    simp only [pinned,Record.LockedPrefixInvariant.view,fileEnv,max_counter]
    apply small cell
    simpa only [pinned,Record.LockedPrefixInvariant.view,fileEnv,HeapLayout.mem_arrange] using member
  all_goals cases live : admission.errorAvailable <;> simp [live,pinned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,
    NativeResourceArc.vmCells,Record.LockedPrefixInvariant.free,errorCell,
    NativeResourceArc.handleType,NativeResourceArc.typeName,NativeResourceArc.termType,
    NativeCodec.typeName,NativeMutex.typeName,NativeFile.typeName,NativeCodec.encode]

/-- Actual resource decoding prepends a fresh Rust owner while retaining the VM
pin, mutex and complete file state in their real heap order. -/
theorem decode_prefix (base : Environment) (poisoned : Bool) (state : State)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ base.nativeResourceTypes) :
    Result.ReadyPrefix (NativeResourceArc.decode (.nativeReference 6)) (pinned base poisoned state)
      (.ok (⟨3,admission.counter + 1⟩ : NativeResourceArc shared_log.LogResource)) (decoded base poisoned state) := by
  have trace := NativeResourceArc.decode_pinned_prefix payload (pinned base poisoned state) 3 5 6
    (pinned_proof base poisoned state) registered
  cases live : admission.errorAvailable <;> simpa [live,List.filter,pinned,decoded,Record.LockedPrefixInvariant.view,fileEnv,
    decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell] using trace

/-- General guarded Rust safety applies to the actual owner-first decoder
layout; no heap normalization or owner erasure is performed. -/
theorem locked_safe (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum : Usize) (value : U16) (valid : Admitted before) (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Safe values) (locked_repair_and_append ⟨1⟩ maximum value)
      (decoded base poisoned before) := by
  have safe := Record.LockedPrefixInvariant.critical_invariant_general base (admission.counter + 1) decodedFrame poisoned before values maximum value
    (by have := admission.bound; omega) (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
    (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
    (by simp [decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell]) valid durable visible
  intro residual world trace
  obtain ⟨⟨state,admitted,v,d,phase⟩,fragment⟩ := safe residual world trace
  refine ⟨?_,fragment⟩
  rcases phase with rfl | rfl | rfl <;>
    exact safe_view _ _ _ _ _ _ (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
      decoded_pins admitted v d

private theorem ownership_decoded (base : Environment) (counter : Nat) (contents : Term) (state : State) :
    NativeResourceArc.ownership (⟨3,admission.counter + 1⟩ : NativeResourceArc shared_log.LogResource)
      (Record.LockedPrefixInvariant.view base counter decodedFrame contents state) = some (2,payload) := by
  cases live : admission.errorAvailable <;> simp [live,List.filter,NativeResourceArc.ownership,Record.LockedPrefixInvariant.view,fileEnv,decodedFrame,pinnedFrame,
    NativeResourceArc.vmCells,errorCell,NativeResourceArc.typeName,NativeResourceArc.handleType,
    NativeResourceArc.termType,NativeCodec.typeName,NativeMutex.typeName,NativeFile.typeName,
    NativeResourceArc.referenceLimit,NativeCodec.roundtrip,NativeIoError.typeName]

/-- The actual first-party resource borrow reaches the verified mutex wrapper
without consuming an owner or changing file state. -/
theorem borrow_safe (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum : Usize) (value : U16) (valid : Admitted before) (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Safe values) (shared_log.repair_append ⟨3,admission.counter + 1⟩ maximum value)
      (decoded base poisoned before) := by
  rw [Record.RepairingLogProperties.critical_contract]
  simp only [NativeResourceArc.deref,Result.nativeGet_bind]
  apply Result.NativeInvariant.nativeGet
  rw [show NativeResourceArc.ownership (⟨3,admission.counter + 1⟩ : NativeResourceArc shared_log.LogResource)
      (decoded base poisoned before) = some (2,payload) from ownership_decoded base (admission.counter + 1) _ before]
  simp only [Result.ok_bind,payload]
  exact locked_safe base poisoned before values maximum value valid durable visible

/-- Every returned Rust result leaves the same file released while both owners
are still live. The facade subsequently consumes only its decoded Rust owner. -/
theorem borrow_returns (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum : Usize) (value : U16) (valid : Admitted before) (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (reply : core.result.Result Bool NativeIoError) (world : Environment)
    (trace : Result.ReadyPrefix (shared_log.repair_append ⟨3,admission.counter + 1⟩ maximum value)
      (decoded base poisoned before) (.ok reply) world) :
    ∃ after, world = Record.LockedPrefixInvariant.view base (admission.counter + 2) decodedFrame
      (Record.LockedPrefixInvariant.free poisoned) after ∧ Admitted after ∧
      Prefix (disk (logBytes values)) after.visible ∧ Prefix (disk (logBytes values)) after.durable := by
  rw [Record.RepairingLogProperties.critical_contract] at trace
  simp only [NativeResourceArc.deref,Result.nativeGet_bind] at trace
  cases trace with
  | nativeGet _ _ _ _ continuation =>
      dsimp only at continuation
      rw [show NativeResourceArc.ownership (⟨3,admission.counter + 1⟩ : NativeResourceArc shared_log.LogResource)
          (decoded base poisoned before) = some (2,payload) from ownership_decoded base (admission.counter + 1) _ before] at continuation
      simp only [Result.ok_bind,payload] at continuation
      exact Record.LockedPrefixInvariant.critical_returns_general base (admission.counter + 1) decodedFrame poisoned before values maximum value
        (by have := admission.bound; omega) (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
        (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
        (by simp [decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell]) valid durable visible reply world continuation

private theorem release_state (base : Environment) (poisoned : Bool) (state : State) :
    NativeResourceArc.ownedState (⟨3,admission.counter + 1⟩ : NativeResourceArc shared_log.LogResource)
      (Record.LockedPrefixInvariant.view base (admission.counter + 2) decodedFrame (Record.LockedPrefixInvariant.free poisoned) state) =
      (.ok none,returned base poisoned false state) := by
  simp only [NativeResourceArc.ownedState,NativeResourceArc.ownerState]
  rw [ownership_decoded]
  cases live : admission.errorAvailable <;> simp [live,returned,
    Record.LockedPrefixInvariant.view,fileEnv,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell,List.filter]

private theorem pinned_pins : ∀ cell ∈ pinCells, cell ∈ pinnedFrame := by
  intro cell member
  simp only [pinCells,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> simp [pinnedFrame,NativeResourceArc.vmCells]

private theorem returned_safe (base : Environment) (poisoned : Bool) (state : State) (values : List U16)
    (valid : Admitted state) (visible : Prefix (disk (logBytes values)) state.visible)
    (durable : Prefix (disk (logBytes values)) state.durable) : Safe values (returned base poisoned false state) := by
  exact safe_view base (admission.counter + 2) pinnedFrame _ state values
    (by simp [Separate,pinnedFrame,NativeResourceArc.vmCells,errorCell]) pinned_pins valid visible durable

private theorem owner_release_safe (base : Environment) (poisoned : Bool) (state : State) (values : List U16)
    (valid : Admitted state) (visible : Prefix (disk (logBytes values)) state.visible)
    (durable : Prefix (disk (logBytes values)) state.durable) :
    Result.NativeInvariant (Safe values)
      (NativeOwnedDrop.drop (⟨3,admission.counter + 1⟩ : NativeResourceArc shared_log.LogResource))
      (Record.LockedPrefixInvariant.view base (admission.counter + 2) decodedFrame (Record.LockedPrefixInvariant.free poisoned) state) := by
  simp only [NativeOwnedDrop.drop,NativeResourceArc.releaseOwned,Result.nativeModify_bind]
  apply Result.NativeInvariant.nativeModify _ _ _
    (safe_view _ _ _ _ _ _ (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
      decoded_pins valid visible durable)
  rw [release_state]
  exact .ok _ _ _ (returned_safe base poisoned state values valid visible durable)

private theorem owner_release_returns (base : Environment) (poisoned : Bool) (state : State) (world : Environment)
    (trace : Result.ReadyPrefix (NativeOwnedDrop.drop (⟨3,admission.counter + 1⟩ : NativeResourceArc shared_log.LogResource))
      (Record.LockedPrefixInvariant.view base (admission.counter + 2) decodedFrame (Record.LockedPrefixInvariant.free poisoned) state)
      (.ok ()) world) : world = returned base poisoned false state := by
  simp only [NativeOwnedDrop.drop,NativeResourceArc.releaseOwned,Result.nativeModify_bind] at trace
  cases trace with
  | nativeModify _ _ actual _ updated _ _ ready continuation =>
      rw [release_state] at ready
      obtain ⟨rfl,rfl⟩ := ready
      cases continuation
      rfl

private theorem returned_without_error_safe (base : Environment) (poisoned : Bool) (state : State) (values : List U16)
    (valid : Admitted state) (visible : Prefix (disk (logBytes values)) state.visible)
    (durable : Prefix (disk (logBytes values)) state.durable) : Safe values (returned base poisoned true state) := by
  apply safe_view base (admission.counter + 2) (NativeResourceArc.vmCells payload 3 5 6) _ state values
    (by simp [Separate,NativeResourceArc.vmCells]) _ valid visible durable
  intro cell member
  simp only [pinCells,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> simp [NativeResourceArc.vmCells]

private theorem error_release_safe (base : Environment) (poisoned : Bool) (state : State) (values : List U16)
    (error : NativeIoError) (valid : Admitted state) (visible : Prefix (disk (logBytes values)) state.visible)
    (durable : Prefix (disk (logBytes values)) state.durable) :
    Result.NativeInvariant (Safe values) (NativeOwnedDrop.drop error) (returned base poisoned false state) := by
  cases error with
  | mk identity =>
      simp only [NativeOwnedDrop.drop,NativeIoError.dispose,Result.consumeNativeCapability]
      apply Result.NativeInvariant.wait _ _ _ (returned_safe base poisoned state values valid visible durable)
      intro actual world ready
      by_cases bounded : identity ≤ 6
      · cases live : admission.errorAvailable <;> interval_cases identity <;>
          simp [live,returned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,
            NativeResourceArc.vmCells,errorCell,List.filter] at ready
        all_goals obtain ⟨rfl,rfl⟩ := ready
        all_goals first
          | simpa [live,returned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,NativeResourceArc.vmCells,errorCell] using
              (Result.NativeInvariant.error (Safe values) .exhausted _ (returned_safe base poisoned state values valid visible durable) :
                Result.NativeInvariant (Safe values) (Result.error .exhausted : Result Unit) (returned base poisoned false state))
          | simpa [live,returned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,NativeResourceArc.vmCells,errorCell] using
              (Result.NativeInvariant.ok (Safe values) () _ (returned_without_error_safe base poisoned state values valid visible durable))
      · have beyond : 6 < identity := by omega
        have positive : identity ≠ 0 := by omega
        have absent (id : Nat) (small : id ≤ 6) : id ≠ identity := by omega
        have absentBool (id : Nat) (small : id ≤ 6) : (id == identity) = false :=
          Bool.eq_false_iff.mpr (fun equal => absent id small (_root_.beq_iff_eq.mp equal))
        cases live : admission.errorAvailable <;> by_cases within : admission.counter + 2 < identity <;>
          simp [live,returned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,
            NativeResourceArc.vmCells,errorCell,List.filter,positive,absentBool,within] at ready
        all_goals obtain ⟨rfl,rfl⟩ := ready
        all_goals simpa [live,returned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,NativeResourceArc.vmCells,errorCell] using
          (Result.NativeInvariant.error (Safe values) .exhausted _ (returned_safe base poisoned state values valid visible durable) :
            Result.NativeInvariant (Safe values) (Result.error .exhausted : Result Unit) (returned base poisoned false state))

/-- A successful error destructor consumes exactly the admitted live capability.
An unavailable or incorrectly typed capability cannot return successfully. -/
private theorem error_release_returns (base : Environment) (poisoned : Bool) (state : State)
    (error : NativeIoError) (world : Environment)
    (trace : Result.ReadyPrefix (NativeOwnedDrop.drop error) (returned base poisoned false state)
      (.ok ()) world) : world = returned base poisoned true state := by
  cases error with
  | mk identity =>
      simp only [NativeOwnedDrop.drop,NativeIoError.dispose,Result.consumeNativeCapability] at trace
      cases trace with
      | wait _ _ actual _ updated _ _ ready continuation =>
          by_cases bounded : identity ≤ 6
          · cases live : admission.errorAvailable <;> interval_cases identity <;>
              simp [live,returned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,
                NativeResourceArc.vmCells,errorCell,List.filter] at ready
            all_goals obtain ⟨rfl,rfl⟩ := ready
            all_goals cases continuation
            all_goals simp [live,returned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,
              NativeResourceArc.vmCells,errorCell]
          · have positive : identity ≠ 0 := by omega
            have absent (id : Nat) (small : id ≤ 6) : id ≠ identity := by omega
            have absentBool (id : Nat) (small : id ≤ 6) : (id == identity) = false :=
              Bool.eq_false_iff.mpr (fun equal => absent id small (_root_.beq_iff_eq.mp equal))
            cases live : admission.errorAvailable <;> by_cases within : admission.counter + 2 < identity <;>
              simp [live,returned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,
                NativeResourceArc.vmCells,errorCell,List.filter,positive,absentBool,within] at ready
            all_goals obtain ⟨rfl,rfl⟩ := ready
            all_goals cases continuation

/-- Successful facade returns expose the exact released resource frame, for
both boolean replies. Every I/O error converted to false has been disposed. -/
theorem facade_returns (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum : U32) (value : U16) (valid : Admitted before)
    (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (accepted : Bool) (world : Environment)
    (trace : Result.ReadyPrefix (__REPAIR_APPEND__ ⟨3,admission.counter + 1⟩ maximum value)
      (decoded base poisoned before) (.ok accepted) world) :
    ∃ state consumed, world = returned base poisoned consumed state ∧ Admitted state ∧
      Prefix (disk (logBytes values)) state.visible ∧ Prefix (disk (logBytes values)) state.durable := by
  rw [Record.RepairingLogProperties.facade_contract] at trace
  simp only [NativeM.lift,Result.ok_bind] at trace
  obtain ⟨reply,middle,borrowed,continuation⟩ := trace.bind_returns
  obtain ⟨state,rfl,admitted,v,d⟩ := borrow_returns base poisoned before values _ value valid durable visible reply middle borrowed
  obtain ⟨releasedUnit,releasedWorld,released,continuation⟩ := continuation.bind_returns
  have identity := owner_release_returns base poisoned state releasedWorld (by cases releasedUnit; exact released)
  subst releasedWorld
  cases reply with
  | Ok answer =>
      cases continuation
      exact ⟨state,false,rfl,admitted,v,d⟩
  | Err error =>
      obtain ⟨releasedUnit,final,disposed,continuation⟩ := continuation.bind_returns
      have identity := error_release_returns base poisoned state error final (by cases releasedUnit; exact disposed)
      subst final
      cases continuation
      exact ⟨state,true,rfl,admitted,v,d⟩

/-- Advance admission by the two fresh identities allocated by a completed
resource call: its temporary Rust owner and its mutex lease. -/
@[expose, instance_reducible] def nextAdmission (consumed : Bool) : Admission :=
  ⟨admission.counter + 2,by have := admission.bound; omega,admission.errorAvailable && !consumed⟩

/-- A completed call is admitted again without resetting allocation counters,
recreating disposed errors, or changing the heap order. -/
theorem returned_pinned (base : Environment) (poisoned consumed : Bool) (state : State) :
    returned base poisoned consumed state = @pinned (nextAdmission consumed) base poisoned state := by
  unfold returned pinned nextAdmission pinnedFrame
  dsimp only
  have fresh (id : Nat) (small : id ≤ 6) : (id == admission.counter + 2 + 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    have := _root_.beq_iff_eq.mp equal
    have := admission.bound
    omega
  cases live : admission.errorAvailable <;> cases consumed <;>
    simp [live,Record.LockedPrefixInvariant.view,fileEnv,HeapLayout.ownerFirst,
      HeapLayout.arrange,NativeResourceArc.vmCells,errorCell,fresh]

/-- The actual compiled facade preserves the known prefix and VM pin on every
native prefix. It consumes its nonfinal owner before converting I/O errors to
false; an unadmitted error destructor exhausts instead of fabricating success. -/
theorem facade_safe (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum : U32) (value : U16) (valid : Admitted before) (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Safe values) (__REPAIR_APPEND__ ⟨3,admission.counter + 1⟩ maximum value)
      (decoded base poisoned before) := by
  rw [Record.RepairingLogProperties.facade_contract]
  simp only [NativeM.lift,Result.ok_bind]
  apply Result.NativeInvariant.bind (computation := shared_log.repair_append ⟨3,admission.counter + 1⟩ (UScalar.cast .Usize maximum) value)
    (borrow_safe base poisoned before values _ value valid durable visible)
  intro reply world completed
  obtain ⟨state,rfl,admitted,v,d⟩ := borrow_returns base poisoned before values _ value valid durable visible reply world completed
  apply Result.NativeInvariant.bind
    (computation := NativeOwnedDrop.drop (⟨3,admission.counter + 1⟩ : NativeResourceArc shared_log.LogResource))
    (owner_release_safe base poisoned state values admitted v d)
  intro releasedUnit world released
  have identity := owner_release_returns base poisoned state world (by cases releasedUnit; exact released)
  subst world
  cases reply with
  | Ok accepted => exact .ok _ _ _ (returned_safe base poisoned state values admitted v d)
  | Err error =>
      apply Result.NativeInvariant.bind (computation := NativeOwnedDrop.drop error)
        (error_release_safe base poisoned state values error admitted v d)
      intro _ final completed
      exact .ok _ _ _ ((error_release_safe base poisoned state values error admitted v d) _ _ completed).1

private theorem pinned_safe (base : Environment) (poisoned : Bool) (state : State) (values : List U16)
    (valid : Admitted state) (visible : Prefix (disk (logBytes values)) state.visible)
    (durable : Prefix (disk (logBytes values)) state.durable) : Safe values (pinned base poisoned state) := by
  exact safe_view base admission.counter pinnedFrame _ state values
    (by simp [Separate,pinnedFrame,NativeResourceArc.vmCells,errorCell]) pinned_pins valid visible durable

private theorem clone_prefix (base : Environment) (poisoned : Bool) (state : State) :
    Result.ReadyPrefix (NativeResourceArc.clone (⟨3,5⟩ : NativeResourceArc shared_log.LogResource))
      (pinned base poisoned state) (.ok (⟨3,admission.counter + 1⟩ : NativeResourceArc shared_log.LogResource)) (decoded base poisoned state) := by
  have pin := pinned_proof base poisoned state
  have trace := NativeResourceArc.clone_live_prefix (⟨3,5⟩ : NativeResourceArc shared_log.LogResource)
    payload 1 (pinned base poisoned state) (by decide) (by decide) pin.owner pin.allocation pin.owners
    (by simp [pinned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,NativeResourceArc.vmCells,errorCell])
  cases live : admission.errorAvailable <;> simpa [live,List.filter,pinned,decoded,Record.LockedPrefixInvariant.view,fileEnv,decodedFrame,pinnedFrame,
    NativeResourceArc.vmCells,errorCell] using trace

private theorem clone_safe (base : Environment) (poisoned : Bool) (state : State) (values : List U16)
    (valid : Admitted state) (visible : Prefix (disk (logBytes values)) state.visible)
    (durable : Prefix (disk (logBytes values)) state.durable) :
    Result.NativeInvariant (Safe values) (NativeResourceArc.clone (⟨3,5⟩ : NativeResourceArc shared_log.LogResource))
      (pinned base poisoned state) := by
  have trace := clone_prefix base poisoned state
  simp only [NativeResourceArc.clone] at trace ⊢
  cases trace with
  | nativeModify _ _ actual _ updated _ _ ready continuation =>
      cases actual with
      | error exception => cases continuation
      | ok owner =>
          cases continuation
          apply Result.NativeInvariant.nativeModify _ _ _ (pinned_safe base poisoned state values valid visible durable)
          dsimp only at ready
          rw [ready]
          exact .ok _ _ _ (safe_view base (admission.counter + 1) decodedFrame _ state values
            (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell]) decoded_pins valid visible durable)

/-- Every decoder prefix retains the VM pin and bytes, including the actual
atomic allocation of the distinct temporary Rust owner. -/
theorem decode_safe (base : Environment) (poisoned : Bool) (state : State) (values : List U16)
    (valid : Admitted state) (visible : Prefix (disk (logBytes values)) state.visible)
    (durable : Prefix (disk (logBytes values)) state.durable)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ base.nativeResourceTypes) :
    Result.NativeInvariant (Safe values) (NativeResourceArc.decode (.nativeReference 6) : NativeM (NativeResourceArc shared_log.LogResource))
      (pinned base poisoned state) := by
  rw [NativeResourceArc.decode_eq]
  apply Result.NativeInvariant.nativeGet
  have registration : NativeResourceArc.typeName shared_log.LogResource ∈ (pinned base poisoned state).nativeResourceTypes := registered
  simp [registration,(pinned_proof base poisoned state).registry]
  exact clone_safe base poisoned state values valid visible durable

private theorem decode_returns (base : Environment) (poisoned : Bool) (state : State)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ base.nativeResourceTypes)
    (owner : NativeResourceArc shared_log.LogResource) (world : Environment)
    (trace : Result.ReadyPrefix (NativeResourceArc.decode (.nativeReference 6)) (pinned base poisoned state) (.ok owner) world) :
    owner = ⟨3,admission.counter + 1⟩ ∧ world = decoded base poisoned state := by
  have expected := (decode_prefix base poisoned state registered).run []
  have actual := trace.run []
  rw [Result.ok_apply] at expected actual
  have equal := expected.symm.trans actual
  simp only [Prod.mk.injEq,Outcome.ok.injEq] at equal
  exact ⟨equal.1.symm,equal.2.symm⟩

/-- Actual resource decoding, compiled native facade, panic conversion and pure
Boolean encoding compose without resetting mutations or losing the VM pin. -/
theorem adapter_safe (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum : U32) (value : U16) (valid : Admitted before) (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ base.nativeResourceTypes) :
    Result.NativeInvariant (Safe values) (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__REPAIR_APPEND__ owner maximum value) Rustler.encodeBool)
      (pinned base poisoned before) := by
  apply Result.NativeInvariant.bind
    (computation := NativeResourceArc.decode (.nativeReference 6))
    (decode_safe base poisoned before values valid visible durable registered)
  intro owner world decodedTrace
  obtain ⟨rfl,rfl⟩ := decode_returns base poisoned before registered owner world decodedTrace
  exact Rustler.executeNative_invariant (facade_safe base poisoned before values maximum value valid durable visible) _

/-- Rejected later arguments release the decoded owner before the mutex has
allocated a lease. The independent VM owner and file bytes are retained. -/
theorem argument_release_safe (base : Environment) (poisoned : Bool) (state : State) (values : List U16)
    (valid : Admitted state) (visible : Prefix (disk (logBytes values)) state.visible)
    (durable : Prefix (disk (logBytes values)) state.durable) :
    Result.NativeInvariant (Safe values)
      (NativeOwnedDrop.drop (⟨3,admission.counter + 1⟩ : NativeResourceArc shared_log.LogResource))
      (decoded base poisoned state) := by
  have released : NativeResourceArc.ownedState (⟨3,admission.counter + 1⟩ : NativeResourceArc shared_log.LogResource)
      (decoded base poisoned state) = (.ok none,
        Record.LockedPrefixInvariant.view base (admission.counter + 1) pinnedFrame (Record.LockedPrefixInvariant.free poisoned) state) := by
    simp only [NativeResourceArc.ownedState,NativeResourceArc.ownerState,decoded]
    rw [ownership_decoded]
    cases live : admission.errorAvailable <;> simp [live,Record.LockedPrefixInvariant.view,fileEnv,decodedFrame,pinnedFrame,
      NativeResourceArc.vmCells,errorCell,List.filter]
  simp only [NativeOwnedDrop.drop,NativeResourceArc.releaseOwned,Result.nativeModify_bind]
  apply Result.NativeInvariant.nativeModify _ _ _
    (safe_view _ _ _ _ _ _ (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
      decoded_pins valid visible durable)
  simp only [decoded] at released
  rw [released]
  exact .ok _ _ _ (safe_view _ _ _ _ _ _
    (by simp [Separate,pinnedFrame,NativeResourceArc.vmCells,errorCell]) pinned_pins valid visible durable)

/-- All scalar conversion outcomes compose with the actual owner cleanup.
Verification exhaustion bypasses the exception handler. -/
private theorem scalar_continuation_safe (base : Environment) (poisoned : Bool) (state : State) (values : List U16)
    (valid : Admitted state) (visible : Prefix (disk (logBytes values)) state.visible)
    (durable : Prefix (disk (logBytes values)) state.durable)
    (reply : Except Exception α) (next : α → Result β)
    (accepted : ∀ value, Result.NativeInvariant (Safe values) (next value) (decoded base poisoned state)) :
    Result.NativeInvariant (Safe values) (do
      let value ← Result.handle (Result.ofExcept reply) (fun error => do
        NativeOwnedDrop.drop (⟨3,admission.counter + 1⟩ : NativeResourceArc shared_log.LogResource)
        Result.error error)
      next value) (decoded base poisoned state) := by
  have safe := argument_release_safe base poisoned state values valid visible durable
  cases reply with
  | ok value => simpa only [Result.ofExcept,Result.handle,Result.ok_bind] using accepted value
  | error exception =>
      cases exception <;> simp only [Result.ofExcept,Result.handle,Result.error_bind,bind_assoc]
      all_goals first
        | exact .error _ _ _ safe.initial
        | apply Result.NativeInvariant.bind safe
          intro _ world trace
          exact .error _ _ _ (safe _ _ trace).1

/-- The complete generated adapter body, for arbitrary scalar terms. -/
@[expose] def termBody (maximum value : Term) : Result Term := do
  let owner ← NativeResourceArc.decode (.nativeReference 6)
  let maximum ← Result.handle (Result.ofExcept (Rustler.decodeUnsigned .U32 32 maximum)) (fun error => do
    NativeOwnedDrop.drop owner
    Result.error error)
  let value ← Result.handle (Result.ofExcept (Rustler.decodeUnsigned .U16 32 value)) (fun error => do
    NativeOwnedDrop.drop owner
    Result.error error)
  Rustler.executeNative (__REPAIR_APPEND__ owner maximum value) Rustler.encodeBool

/-- Every scalar term is covered, including range/narrowing behavior and cleanup
when either conversion fails after resource decoding. -/
theorem term_body_safe (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum value : Term) (valid : Admitted before) (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ base.nativeResourceTypes) :
    Result.NativeInvariant (Safe values) (termBody maximum value) (pinned base poisoned before) := by
  unfold termBody
  apply Result.NativeInvariant.bind (computation := NativeResourceArc.decode (.nativeReference 6))
    (decode_safe base poisoned before values valid visible durable registered)
  intro owner world trace
  obtain ⟨rfl,rfl⟩ := decode_returns base poisoned before registered owner world trace
  apply scalar_continuation_safe base poisoned before values valid visible durable
  intro decodedMaximum
  apply scalar_continuation_safe base poisoned before values valid visible durable
  intro decodedValue
  exact Rustler.executeNative_invariant
    (facade_safe base poisoned before values decodedMaximum decodedValue valid durable visible) _

/-- Atomic registration followed by the full generated decoding/execution body
retains the known bytes and VM pin; initial registration need not be assumed. -/
theorem term_adapter_safe (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum value : Term) (valid : Admitted before) (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Safe values)
      (Rustler.withResourceTypes [NativeResourceArc.typeName shared_log.LogResource] (termBody maximum value))
      (pinned base poisoned before) := by
  unfold Rustler.withResourceTypes
  apply Result.NativeInvariant.nativeModify _ _ _ (pinned_safe base poisoned before values valid visible durable)
  let registered := {base with nativeResourceTypes :=
    (base.nativeResourceTypes ++ [NativeResourceArc.typeName shared_log.LogResource]).eraseDups}
  change Result.NativeInvariant (Safe values) (termBody maximum value) (pinned registered poisoned before)
  exact term_body_safe registered poisoned before values maximum value valid durable visible (by simp [registered])

/-- Failed scalar conversion cannot produce a successful native return, even
when its error handler releases the resource before propagating the exception. -/
private theorem scalar_continuation_returns (owner : NativeResourceArc shared_log.LogResource)
    (reply : Except Exception α) (next : α → Result β) (before after : Environment) (result : β)
    (trace : Result.ReadyPrefix (do
      let value ← Result.handle (Result.ofExcept reply) (fun error => do
        NativeOwnedDrop.drop owner
        Result.error error)
      next value) before (.ok result) after) :
    ∃ value, Result.ReadyPrefix (next value) before (.ok result) after := by
  cases reply with
  | ok value => exact ⟨value,trace⟩
  | error exception =>
      cases exception <;> simp only [Result.ofExcept,Result.handle,Result.error_bind,bind_assoc] at trace
      all_goals first
        | obtain ⟨_,_,_,impossible⟩ := trace.bind_returns
          cases impossible
        | cases trace

/-- Every successful term return comes from the actual facade and can be used
as admission for a subsequent call. Invalid scalars never fabricate success. -/
theorem term_body_returns (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum value result : Term) (valid : Admitted before)
    (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ base.nativeResourceTypes)
    (world : Environment)
    (trace : Result.ReadyPrefix (termBody maximum value) (pinned base poisoned before) (.ok result) world) :
    ∃ state consumed accepted, result = Rustler.encodeBool accepted ∧
      world = @pinned (nextAdmission consumed) base poisoned state ∧ Admitted state ∧
      Prefix (disk (logBytes values)) state.visible ∧ Prefix (disk (logBytes values)) state.durable := by
  unfold termBody at trace
  obtain ⟨owner,decodedWorld,decodedTrace,trace⟩ := trace.bind_returns
  obtain ⟨rfl,rfl⟩ := decode_returns base poisoned before registered owner decodedWorld decodedTrace
  obtain ⟨maximum,trace⟩ := scalar_continuation_returns _ _ _ _ _ _ trace
  obtain ⟨value,trace⟩ := scalar_continuation_returns _ _ _ _ _ _ trace
  obtain ⟨accepted,encoded,returned⟩ := Rustler.executeNative_returns trace
  obtain ⟨state,consumed,identity,admitted,v,d⟩ :=
    facade_returns base poisoned before values maximum value valid durable visible accepted world returned
  exact ⟨state,consumed,accepted,encoded,identity.trans (returned_pinned base poisoned consumed state),admitted,v,d⟩

/-- Resource registration is retained in the next call's base environment. -/
@[expose] def registeredBase (base : Environment) : Environment :=
  {base with nativeResourceTypes :=
    (base.nativeResourceTypes ++ [NativeResourceArc.typeName shared_log.LogResource]).eraseDups}

theorem term_adapter_returns (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum value result : Term) (valid : Admitted before)
    (durable : Prefix (disk (logBytes values)) before.durable)
    (visible : Prefix (disk (logBytes values)) before.visible) (world : Environment)
    (trace : Result.ReadyPrefix
      (Rustler.withResourceTypes [NativeResourceArc.typeName shared_log.LogResource] (termBody maximum value))
      (pinned base poisoned before) (.ok result) world) :
    ∃ state consumed accepted, result = Rustler.encodeBool accepted ∧
      world = @pinned (nextAdmission consumed) (registeredBase base) poisoned state ∧ Admitted state ∧
      Prefix (disk (logBytes values)) state.visible ∧ Prefix (disk (logBytes values)) state.durable := by
  unfold Rustler.withResourceTypes at trace
  cases trace with
  | nativeModify _ _ actual _ updated _ _ ready continuation =>
      obtain ⟨rfl,rfl⟩ := ready
      exact term_body_returns (registeredBase base) poisoned before values maximum value result valid durable visible
        (by simp [registeredBase]) world continuation

end Record.GuardedRepairAdapter
