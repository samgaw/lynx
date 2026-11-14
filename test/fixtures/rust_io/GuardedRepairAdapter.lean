module
public import Record.LockedPrefixInvariant
public import Record.RepairingLogProperties
public import Record.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.GuardedRepairAdapter
open NativeFile Record.Properties Record.ResizeProperties Record.LogProperties Record.RepairCrashProperties Record.CrashProperties

local instance ownerLayout : HeapLayout := HeapLayout.ownerFirst 7

@[expose] def payload : shared_log.LogResource := ⟨⟨1⟩⟩
@[expose] def pinCells : List (Nat × String × Term) := [
  (5,NativeResourceArc.handleType shared_log.LogResource,.nativeReference 3),
  (6,NativeResourceArc.termType shared_log.LogResource,.tuple #[.nativeReference 3,.nativeReference 5])]
@[expose] def errorCell : Nat × String × Term := (4,NativeIoError.typeName,.atom "live")
@[expose] def pinnedFrame : List (Nat × String × Term) := NativeResourceArc.vmCells payload 3 5 6 ++ [errorCell]
@[expose] def decodedFrame : List (Nat × String × Term) :=
  (7,NativeResourceArc.handleType shared_log.LogResource,.nativeReference 3) :: pinnedFrame.map (fun cell =>
    if cell.1 = 3 then (3,NativeResourceArc.typeName shared_log.LogResource,
      .tuple #[.integer 2,NativeCodec.encode payload]) else cell)
@[expose] def pinned (base : Environment) (poisoned : Bool) (state : State) : Environment :=
  Record.LockedPrefixInvariant.view base 6 pinnedFrame (Record.LockedPrefixInvariant.free poisoned) state
@[expose] def decoded (base : Environment) (poisoned : Bool) (state : State) : Environment :=
  Record.LockedPrefixInvariant.view base 7 decodedFrame (Record.LockedPrefixInvariant.free poisoned) state
@[expose] def returned (base : Environment) (poisoned consumed : Bool) (state : State) : Environment :=
  Record.LockedPrefixInvariant.view base 8
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
    simp only [pinned,Record.LockedPrefixInvariant.view,fileEnv,HeapLayout.mem_arrange,
      pinnedFrame,NativeResourceArc.vmCells,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pinned,Record.LockedPrefixInvariant.view,fileEnv,errorCell]
  all_goals simp [pinned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,
    NativeResourceArc.vmCells,Record.LockedPrefixInvariant.free,errorCell,
    NativeResourceArc.handleType,NativeResourceArc.typeName,NativeResourceArc.termType,
    NativeCodec.typeName,NativeMutex.typeName,NativeFile.typeName,NativeCodec.encode]

/-- Actual resource decoding prepends a fresh Rust owner while retaining the VM
pin, mutex and complete file state in their real heap order. -/
theorem decode_prefix (base : Environment) (poisoned : Bool) (state : State)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ base.nativeResourceTypes) :
    Result.ReadyPrefix (NativeResourceArc.decode (.nativeReference 6)) (pinned base poisoned state)
      (.ok (⟨3,7⟩ : NativeResourceArc shared_log.LogResource)) (decoded base poisoned state) := by
  have trace := NativeResourceArc.decode_pinned_prefix payload (pinned base poisoned state) 3 5 6
    (pinned_proof base poisoned state) registered
  simpa [pinned,decoded,Record.LockedPrefixInvariant.view,fileEnv,
    decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell] using trace

/-- General guarded Rust safety applies to the actual owner-first decoder
layout; no heap normalization or owner erasure is performed. -/
theorem locked_safe (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum : Usize) (value : U16) (valid : Admitted before) (stable : before.durable = before.visible)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Safe values) (locked_repair_and_append ⟨1⟩ maximum value)
      (decoded base poisoned before) := by
  have safe := Record.LockedPrefixInvariant.critical_invariant base 7 decodedFrame poisoned before values maximum value
    (by decide) (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
    (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
    (by decide) valid stable visible
  intro residual world trace
  obtain ⟨⟨state,admitted,v,d,phase⟩,fragment⟩ := safe residual world trace
  refine ⟨?_,fragment⟩
  rcases phase with rfl | rfl | rfl <;>
    exact safe_view _ _ _ _ _ _ (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
      decoded_pins admitted v d

private theorem ownership_decoded (base : Environment) (counter : Nat) (contents : Term) (state : State) :
    NativeResourceArc.ownership (⟨3,7⟩ : NativeResourceArc shared_log.LogResource)
      (Record.LockedPrefixInvariant.view base counter decodedFrame contents state) = some (2,payload) := by
  simp [NativeResourceArc.ownership,Record.LockedPrefixInvariant.view,fileEnv,decodedFrame,pinnedFrame,
    NativeResourceArc.vmCells,errorCell,NativeResourceArc.typeName,NativeResourceArc.handleType,
    NativeResourceArc.termType,NativeCodec.typeName,NativeMutex.typeName,NativeFile.typeName,
    NativeResourceArc.referenceLimit,NativeCodec.roundtrip]

/-- The actual first-party resource borrow reaches the verified mutex wrapper
without consuming an owner or changing file state. -/
theorem borrow_safe (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum : Usize) (value : U16) (valid : Admitted before) (stable : before.durable = before.visible)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Safe values) (shared_log.repair_append ⟨3,7⟩ maximum value)
      (decoded base poisoned before) := by
  rw [Record.RepairingLogProperties.critical_contract]
  simp only [NativeResourceArc.deref,Result.nativeGet_bind]
  apply Result.NativeInvariant.nativeGet
  rw [show NativeResourceArc.ownership (⟨3,7⟩ : NativeResourceArc shared_log.LogResource)
      (decoded base poisoned before) = some (2,payload) from ownership_decoded base 7 _ before]
  simp only [Result.ok_bind,payload]
  exact locked_safe base poisoned before values maximum value valid stable visible

/-- Every returned Rust result leaves the same file released while both owners
are still live. The facade subsequently consumes only its decoded Rust owner. -/
theorem borrow_returns (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum : Usize) (value : U16) (valid : Admitted before) (stable : before.durable = before.visible)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (reply : core.result.Result Bool NativeIoError) (world : Environment)
    (trace : Result.ReadyPrefix (shared_log.repair_append ⟨3,7⟩ maximum value)
      (decoded base poisoned before) (.ok reply) world) :
    ∃ after, world = Record.LockedPrefixInvariant.view base 8 decodedFrame
      (Record.LockedPrefixInvariant.free poisoned) after ∧ Admitted after ∧
      Prefix (disk (logBytes values)) after.visible ∧ Prefix (disk (logBytes values)) after.durable := by
  rw [Record.RepairingLogProperties.critical_contract] at trace
  simp only [NativeResourceArc.deref,Result.nativeGet_bind] at trace
  cases trace with
  | nativeGet _ _ _ _ continuation =>
      dsimp only at continuation
      rw [show NativeResourceArc.ownership (⟨3,7⟩ : NativeResourceArc shared_log.LogResource)
          (decoded base poisoned before) = some (2,payload) from ownership_decoded base 7 _ before] at continuation
      simp only [Result.ok_bind,payload] at continuation
      exact Record.LockedPrefixInvariant.critical_returns base 7 decodedFrame poisoned before values maximum value
        (by decide) (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
        (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
        (by decide) valid stable visible reply world continuation

private theorem release_state (base : Environment) (poisoned : Bool) (state : State) :
    NativeResourceArc.ownedState (⟨3,7⟩ : NativeResourceArc shared_log.LogResource)
      (Record.LockedPrefixInvariant.view base 8 decodedFrame (Record.LockedPrefixInvariant.free poisoned) state) =
      (.ok none,returned base poisoned false state) := by
  simp only [NativeResourceArc.ownedState,NativeResourceArc.ownerState]
  rw [ownership_decoded]
  simp [returned,
    Record.LockedPrefixInvariant.view,fileEnv,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell,List.filter]

private theorem pinned_pins : ∀ cell ∈ pinCells, cell ∈ pinnedFrame := by
  intro cell member
  simp only [pinCells,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> simp [pinnedFrame,NativeResourceArc.vmCells]

private theorem returned_safe (base : Environment) (poisoned : Bool) (state : State) (values : List U16)
    (valid : Admitted state) (visible : Prefix (disk (logBytes values)) state.visible)
    (durable : Prefix (disk (logBytes values)) state.durable) : Safe values (returned base poisoned false state) := by
  exact safe_view base 8 pinnedFrame _ state values
    (by simp [Separate,pinnedFrame,NativeResourceArc.vmCells,errorCell]) pinned_pins valid visible durable

private theorem owner_release_safe (base : Environment) (poisoned : Bool) (state : State) (values : List U16)
    (valid : Admitted state) (visible : Prefix (disk (logBytes values)) state.visible)
    (durable : Prefix (disk (logBytes values)) state.durable) :
    Result.NativeInvariant (Safe values)
      (NativeOwnedDrop.drop (⟨3,7⟩ : NativeResourceArc shared_log.LogResource))
      (Record.LockedPrefixInvariant.view base 8 decodedFrame (Record.LockedPrefixInvariant.free poisoned) state) := by
  simp only [NativeOwnedDrop.drop,NativeResourceArc.releaseOwned,Result.nativeModify_bind]
  apply Result.NativeInvariant.nativeModify _ _ _
    (safe_view _ _ _ _ _ _ (by simp [Separate,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,errorCell])
      decoded_pins valid visible durable)
  rw [release_state]
  exact .ok _ _ _ (returned_safe base poisoned state values valid visible durable)

private theorem owner_release_returns (base : Environment) (poisoned : Bool) (state : State) (world : Environment)
    (trace : Result.ReadyPrefix (NativeOwnedDrop.drop (⟨3,7⟩ : NativeResourceArc shared_log.LogResource))
      (Record.LockedPrefixInvariant.view base 8 decodedFrame (Record.LockedPrefixInvariant.free poisoned) state)
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
  apply safe_view base 8 (NativeResourceArc.vmCells payload 3 5 6) _ state values
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
      by_cases bounded : identity ≤ 8
      · interval_cases identity <;>
          simp [returned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,
            NativeResourceArc.vmCells,errorCell,List.filter] at ready
        all_goals obtain ⟨rfl,rfl⟩ := ready
        all_goals first
          | exact .error _ _ _ (returned_safe base poisoned state values valid visible durable)
          | exact .ok _ _ _ (returned_without_error_safe base poisoned state values valid visible durable)
      · have beyond : 8 < identity := by omega
        simp [returned,Record.LockedPrefixInvariant.view,fileEnv,beyond] at ready
        obtain ⟨rfl,rfl⟩ := ready
        exact .error _ _ _ (returned_safe base poisoned state values valid visible durable)

/-- The actual compiled facade preserves the known prefix and VM pin on every
native prefix. It consumes its nonfinal owner before converting I/O errors to
false; an unadmitted error destructor exhausts instead of fabricating success. -/
theorem facade_safe (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum : U32) (value : U16) (valid : Admitted before) (stable : before.durable = before.visible)
    (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (Safe values) (__REPAIR_APPEND__ ⟨3,7⟩ maximum value)
      (decoded base poisoned before) := by
  rw [Record.RepairingLogProperties.facade_contract]
  simp only [NativeM.lift,Result.ok_bind]
  apply Result.NativeInvariant.bind (computation := shared_log.repair_append ⟨3,7⟩ (UScalar.cast .Usize maximum) value)
    (borrow_safe base poisoned before values _ value valid stable visible)
  intro reply world completed
  obtain ⟨state,rfl,admitted,v,d⟩ := borrow_returns base poisoned before values _ value valid stable visible reply world completed
  apply Result.NativeInvariant.bind
    (computation := NativeOwnedDrop.drop (⟨3,7⟩ : NativeResourceArc shared_log.LogResource))
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
  exact safe_view base 6 pinnedFrame _ state values
    (by simp [Separate,pinnedFrame,NativeResourceArc.vmCells,errorCell]) pinned_pins valid visible durable

private theorem clone_prefix (base : Environment) (poisoned : Bool) (state : State) :
    Result.ReadyPrefix (NativeResourceArc.clone (⟨3,5⟩ : NativeResourceArc shared_log.LogResource))
      (pinned base poisoned state) (.ok (⟨3,7⟩ : NativeResourceArc shared_log.LogResource)) (decoded base poisoned state) := by
  have pin := pinned_proof base poisoned state
  have trace := NativeResourceArc.clone_live_prefix (⟨3,5⟩ : NativeResourceArc shared_log.LogResource)
    payload 1 (pinned base poisoned state) (by decide) (by decide) pin.owner pin.allocation pin.owners
    (by simp [pinned,Record.LockedPrefixInvariant.view,fileEnv,pinnedFrame,NativeResourceArc.vmCells,errorCell])
  simpa [pinned,decoded,Record.LockedPrefixInvariant.view,fileEnv,decodedFrame,pinnedFrame,
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
          exact .ok _ _ _ (safe_view base 7 decodedFrame _ state values
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
    owner = ⟨3,7⟩ ∧ world = decoded base poisoned state := by
  have expected := (decode_prefix base poisoned state registered).run []
  have actual := trace.run []
  rw [Result.ok_apply] at expected actual
  have equal := expected.symm.trans actual
  simp only [Prod.mk.injEq,Outcome.ok.injEq] at equal
  exact ⟨equal.1.symm,equal.2.symm⟩

/-- Actual resource decoding, compiled native facade, panic conversion and pure
Boolean encoding compose without resetting mutations or losing the VM pin. -/
theorem adapter_safe (base : Environment) (poisoned : Bool) (before : State) (values : List U16)
    (maximum : U32) (value : U16) (valid : Admitted before) (stable : before.durable = before.visible)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ base.nativeResourceTypes) :
    Result.NativeInvariant (Safe values) (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__REPAIR_APPEND__ owner maximum value) Rustler.encodeBool)
      (pinned base poisoned before) := by
  have durable : Prefix (disk (logBytes values)) before.durable := stable ▸ visible
  apply Result.NativeInvariant.bind
    (computation := NativeResourceArc.decode (.nativeReference 6))
    (decode_safe base poisoned before values valid visible durable registered)
  intro owner world decodedTrace
  obtain ⟨rfl,rfl⟩ := decode_returns base poisoned before registered owner world decodedTrace
  exact Rustler.executeNative_invariant (facade_safe base poisoned before values maximum value valid stable visible) _

end Record.GuardedRepairAdapter
