module
public import ResourceAwait.Critical
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace ResourceAwait.Properties

@[expose] def initial (amount : U64) : resource_suspending.closure :=
  ⟨some ⟨2,3⟩, amount, 0#u32, none, none, none, none⟩
@[expose] def pending (amount : U64) : resource_suspending.closure :=
  ⟨none, amount, 3#u32, some ⟨2,3⟩, some amount, some ⟨false, ⟨amount⟩⟩, some true⟩
@[expose] def completed (amount : U64) : resource_suspending.closure :=
  ⟨none, amount, 1#u32, none, some amount, some ⟨false, ⟨amount⟩⟩, some false⟩
@[expose] def cell (value : U64) : Nat × String × Term :=
  (1, NativeMutex.typeName effects_core.Counter,
    .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode ({value} : effects_core.Counter)])
@[expose] def live (env : Environment) (value : U64) (counter : Nat) (notified : Bool) : Environment :=
  {env with nativeRefCounter := counter, nativeHeap := [
    (3, NativeResourceArc.handleType CounterResource, .nativeReference 2),
    (2, NativeResourceArc.typeName CounterResource,
      .tuple #[.integer 1, NativeCodec.encode ({state := ⟨1⟩} : CounterResource)]), cell value,
    (0, NativeWaker.typeName, .atom (if notified then "notified" else "idle"))]}
@[expose] def cleaned (env : Environment) (counter : Nat) (notified : Bool) : Environment :=
  {env with nativeRefCounter := counter, nativeHeap := [
    (3, NativeResourceArc.handleType CounterResource, .nativeReference 2),
    (2, NativeResourceArc.typeName CounterResource,
      .tuple #[.integer 1, NativeCodec.encode ({state := ⟨1⟩} : CounterResource)]),
    (0, NativeWaker.typeName, .atom (if notified then "notified" else "idle"))]}
@[expose] def reclaimed (env : Environment) (counter : Nat) (notified : Bool) : Environment :=
  {env with nativeRefCounter := counter, nativeHeap := [
    (0, NativeWaker.typeName, .atom (if notified then "notified" else "idle"))]}

theorem initial_state (amount : U64) :
    resource_suspending ⟨2,3⟩ amount = Result.ok (initial amount) := rfl

theorem release_next {α : Type} (value : U64) (counter : Nat) (notified : Bool)
    (env : Environment) (next : Unit → NativeM α) :
    (resource_release ⟨2,3⟩ >>= next) (live env value counter notified) =
      next () (reclaimed env counter notified) := by
  have cleanup : ∀ next : NativeM α,
      (do NativeResourceCleanup.cleanup ({state := ⟨1⟩} : CounterResource); next)
        (live env value counter notified) = next (cleaned env counter notified) := by
    intro next
    simp [NativeResourceCleanup.cleanup, CounterResource.drop_owned, NativeOwnedDrop.drop,
      NativeMutex.dispose, NativeM.readCell, NativeM.removeCell, NativeM.ok,
      live, cleaned, cell, NativeCodec.roundtrip, List.filter]
  have result := NativeResourceArc.releaseOwned_last_run_next
    (⟨2,3⟩ : NativeResourceArc CounterResource) ⟨⟨1⟩⟩ next
    (live env value counter notified) (cleaned env counter notified)
    (by simp [live, cell]) (by simp [live, cell])
    (by simp [live, cell, NativeMutex.typeName, NativeResourceArc.handleType,
      NativeResourceArc.typeName, NativeWaker.typeName]) cleanup
    (by simp [cleaned]) (by simp [cleaned])
    (by simp [cleaned, NativeResourceArc.handleType, NativeResourceArc.typeName, NativeWaker.typeName])
  simpa [resource_release, NativeOwnedDrop.drop, cleaned, reclaimed] using result

theorem drop_unstarted (value amount : U64) (env : Environment) :
    resource_suspending.closure.drop_owned (initial amount) (live env value 3 false) =
      (.ok (), reclaimed env 3 false) := by
  have body : resource_suspending.closure.drop_owned (initial amount) = resource_release ⟨2,3⟩ := rfl
  rw [body]
  simpa using release_next value 3 false env Result.ok

theorem first_pending_next {α : Type} (value amount : U64) (env : Environment)
    (next : (core.task.poll.Poll Bool × effects_native.core.pin.Pin resource_suspending.closure × NativeTaskContext) → Result α) :
    (resource_suspending.closure.poll ⟨initial amount⟩ ⟨⟨0, false⟩⟩ >>= next) (live env value 3 false) =
      next (.Pending, ⟨pending amount⟩, ⟨⟨0, false⟩⟩) (live env value 3 true) := by
  have body : resource_suspending.closure.poll ⟨initial amount⟩ ⟨⟨0, false⟩⟩ = (do
      NativeWaker.wakeByRef ⟨0, false⟩
      Result.ok (.Pending, ⟨pending amount⟩, ⟨⟨0, false⟩⟩)) := by
    simp [resource_suspending.closure.poll, initial, pending, core.mem.replace,
      effects_core.paused_counter, core.future.into_future.IntoFuture.Blanket.into_future,
      effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
      core.pin.PinMutAT.get_mut, NativeM.ok, bind_assoc, UScalar.ofNatCore, UScalar.val]
  rw [body]
  simp only [bind_assoc, Result.ok_bind]
  have woke := NativeWaker.wakeByRef_registered_next ⟨0, false⟩
    (fun _ => next (.Pending, ⟨pending amount⟩, ⟨⟨0, false⟩⟩)) (live env value 3 false)
    (by simp [live]) (by simp [live, cell]) rfl
  simpa [NativeWaker.notifiedEnv, live, cell] using woke

theorem cancel_pending (value amount : U64) (env : Environment) :
    resource_suspending.closure.drop_owned (pending amount) (live env value 3 true) =
      (.ok (), reclaimed env 3 true) := by
  have body : resource_suspending.closure.drop_owned (pending amount) = resource_release ⟨2,3⟩ := rfl
  rw [body]
  simpa using release_next value 3 true env Result.ok

theorem completed_drop (amount : U64) :
    resource_suspending.closure.drop_owned (completed amount) = Result.ok () := rfl

theorem update_next {α : Type} (value amount : U64) (env : Environment) (notified : Bool)
    (next : Bool → NativeM α) :
    ∃ changed updated,
      (resource_locked_increment ⟨2,3⟩ amount >>= next) (live env value 3 notified) =
        next changed (live env updated 4 notified) ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  obtain ⟨changed, updated, computed, arithmetic⟩ := ResourceAwait.Critical.critical_state_next
    next (⟨1⟩ : NativeMutex effects_core.Counter) ⟨value⟩ amount false (live env value 3 notified)
    (by simp [List.filter, live, cell]) (by simp [live, cell])
  refine ⟨changed, updated.value, ?_, ?_⟩
  · have observed := NativeResourceArc.deref_single_next
      (⟨2,3⟩ : NativeResourceArc CounterResource) ⟨⟨1⟩⟩
      (fun payload => effects_core.locked_increment payload.state amount >>= next) (live env value 3 notified)
      (by simp [List.filter, live, cell]) (by simp [List.filter, live, cell])
      (by simp [List.filter, live, cell, NativeMutex.typeName,
        NativeResourceArc.typeName, NativeResourceArc.handleType, NativeWaker.typeName])
    simp only [resource_locked_increment, monadLift_self, bind_assoc]
    dsimp only at observed
    rw [observed]
    cases updated
    simpa [live, cell, List.map] using computed
  · cases changed <;> cases updated <;> simpa using arithmetic

theorem resume_next {α : Type} (value amount : U64) (env : Environment) (notified : Bool)
    (next : (core.task.poll.Poll Bool × effects_native.core.pin.Pin resource_suspending.closure × NativeTaskContext) → Result α) :
    ∃ changed updated,
      (resource_suspending.closure.poll ⟨pending amount⟩ ⟨⟨0, false⟩⟩ >>= next) (live env value 3 notified) =
        next (.Ready changed, ⟨completed amount⟩, ⟨⟨0, false⟩⟩) (reclaimed env 4 notified) ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  have body : resource_suspending.closure.poll ⟨pending amount⟩ ⟨⟨0, false⟩⟩ = (do
      let changed ← resource_locked_increment ⟨2,3⟩ amount
      resource_release ⟨2,3⟩
      Result.ok (.Ready changed, ⟨completed amount⟩, ⟨⟨0, false⟩⟩)) := by
    simp [resource_suspending.closure.poll, pending, completed, core.mem.replace,
      effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
      effects_core.saturating_increment, core.pin.PinMutAT.get_mut, NativeM.ok,
      UScalar.ofNatCore, UScalar.val, bind_assoc]
  let finish : Bool → NativeM α := fun changed => do
    resource_release ⟨2,3⟩
    next (.Ready changed, ⟨completed amount⟩, ⟨⟨0, false⟩⟩)
  obtain ⟨changed, updated, computed, arithmetic⟩ := update_next value amount env notified finish
  refine ⟨changed, updated, ?_, arithmetic⟩
  rw [body]
  simp only [bind_assoc, Result.ok_bind]
  change (resource_locked_increment ⟨2,3⟩ amount >>= finish) _ = _
  rw [computed]
  exact release_next updated 4 notified env _

theorem suspend_then_cancel (value amount : U64) (env : Environment) :
    (do
      let (_, future, _) ← resource_suspending.closure.poll ⟨initial amount⟩ ⟨⟨0, false⟩⟩
      resource_suspending.closure.drop_owned future.pointer) (live env value 3 false) =
        (.ok (), reclaimed env 3 true) := by
  rw [first_pending_next]
  exact cancel_pending value amount env

theorem missing_capture (amount : U64) :
    resource_suspending.closure.drop_owned {initial amount with _0 := none} =
      Result.error .exhausted := rfl

theorem missing_saved_owner (amount : U64) :
    resource_suspending.closure.drop_owned {pending amount with saved_0 := none} =
      Result.error .exhausted := rfl

end ResourceAwait.Properties
