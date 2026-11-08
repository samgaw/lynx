module
public import ResourceAwait.Properties
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace ResourceAwait.Task
open ResourceAwait.Properties

/-- Only the Poll representation is adapted; execution uses the extracted body. -/
@[expose] def adapt
    (implementation : effects_native.core.pin.Pin resource_suspending.closure → NativeTaskContext →
      NativeM (core.task.poll.Poll Bool × effects_native.core.pin.Pin resource_suspending.closure × NativeTaskContext))
    (state : resource_suspending.closure) (context : NativeTaskContext) :
    NativeM (NativeTask.Step Bool resource_suspending.closure) := do
  let (reply, future, updatedContext) ← implementation ⟨state⟩ context
  match reply with
  | .Pending => .ok (.pending future.pointer updatedContext)
  | .Ready value => .ok (.ready value future.pointer)

theorem poll_bind {α : Type} (state : resource_suspending.closure) (context : NativeTaskContext)
    (next : NativeTask.Step Bool resource_suspending.closure → NativeM α) :
    (adapt resource_suspending.closure.poll state context >>= next) = (do
      let (reply, future, updatedContext) ← resource_suspending.closure.poll ⟨state⟩ context
      match reply with
      | .Pending => next (.pending future.pointer updatedContext)
      | .Ready value => next (.ready value future.pointer)) := by
  simp only [adapt, bind_assoc]
  congr 1
  funext triple
  rcases triple with ⟨reply, future, context⟩
  cases reply <;> simp [NativeM.ok]

theorem first_poll_next {α : Type} (value amount : U64) (env : Environment)
    (next : NativeTask.Step Bool resource_suspending.closure → NativeM α) :
    (adapt resource_suspending.closure.poll (initial amount) ⟨⟨0, false⟩⟩ >>= next) (live env value 3 false) =
      next (.pending (pending amount) ⟨⟨0, false⟩⟩) (live env value 3 true) := by
  rw [poll_bind, first_pending_next]

theorem resume_poll_next {α : Type} (value amount : U64) (env : Environment)
    (next : NativeTask.Step Bool resource_suspending.closure → NativeM α) :
    ∃ changed updated,
      (adapt resource_suspending.closure.poll (pending amount) ⟨⟨0, false⟩⟩ >>= next) (live env value 3 false) =
        next (.ready changed (completed amount)) (reclaimed env 4 false) ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  rw [poll_bind]
  exact resume_next value amount env false
    (fun (reply, future, context) => do
      match reply with
      | .Pending => next (.pending future.pointer context)
      | .Ready changed => next (.ready changed future.pointer))

theorem completion (value amount : U64) (env : Environment) :
    ∃ changed updated,
      NativeTask.drive (adapt resource_suspending.closure.poll)
      resource_suspending.closure.drop_owned (fun _ => false) ⟨⟨0, false⟩⟩ 2 (initial amount) (live env value 3 false) =
        (.ok (some changed), reclaimed env 4 false) ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  simp only [NativeTask.drive]
  simp only [first_poll_next]
  simp only [NativeWaker.await_notified_next ⟨0, false⟩ (fun _ => false) _ (live env value 3 true) (by simp [live]) rfl (by simp [live, cell]) rfl]
  have consumed : {live env value 3 true with
      nativeHeap := (live env value 3 true).nativeHeap.map fun cell =>
        if cell.1 == 0 then (0, NativeWaker.typeName, .atom "idle") else cell} = live env value 3 false := by
    simp [live, cell]
  rw [consumed]
  obtain ⟨changed, updated, computed, arithmetic⟩ := resume_poll_next value amount env
    (fun step => do
      match step with
      | .ready value finished => resource_suspending.closure.drop_owned finished; Result.ok (some value)
      | .pending retained context => do
        match ← NativeWaker.await context.waker (fun _ => false) with
        | .wake => NativeTask.drive (adapt resource_suspending.closure.poll) resource_suspending.closure.drop_owned (fun _ => false) context 0 retained
        | .cancel => resource_suspending.closure.drop_owned retained; Result.ok none)
  refine ⟨changed, updated, ?_, arithmetic⟩
  simp only [NativeTask.drive, NativeM.ok, completed_drop, Result.ok_bind, Result.ok_apply] at computed ⊢
  convert computed using 1
  congr 1
  congr 1
  funext step
  cases step <;> rfl

theorem cancellation (value amount : U64) (env : Environment) :
    NativeTask.drive (adapt resource_suspending.closure.poll)
      resource_suspending.closure.drop_owned (fun _ => true) ⟨⟨0, false⟩⟩ 2 (initial amount) (live env value 3 false) =
      (.ok none, reclaimed env 3 true) := by
  simp only [NativeTask.drive]
  simp only [first_poll_next]
  simp only [NativeWaker.await_cancelled_next ⟨0, false⟩ (fun _ => true) _ (live env value 3 true) (by simp [live]) rfl (by simp [live, cell]) rfl]
  change (resource_release ⟨2,3⟩ >>= fun _ => Result.ok none) _ = _
  simpa using release_next value 3 true env (fun _ => Result.ok (none : Option Bool))

theorem cutoff_zero (amount : U64) :
    NativeTask.drive (adapt resource_suspending.closure.poll)
      resource_suspending.closure.drop_owned (fun _ => false) ⟨⟨0, false⟩⟩ 0 (initial amount) = Result.error .exhausted := rfl

/-- One Pending poll cannot become a completed task when the poll budget ends. -/
theorem cutoff_one (value amount : U64) (env : Environment) :
    NativeTask.drive (adapt resource_suspending.closure.poll)
      resource_suspending.closure.drop_owned (fun _ => false) ⟨⟨0, false⟩⟩ 1 (initial amount) (live env value 3 false) =
      (.error .exhausted, live env value 3 false) := by
  simp only [NativeTask.drive]
  simp only [first_poll_next]
  simp only [NativeWaker.await_notified_next ⟨0, false⟩ (fun _ => false) _ (live env value 3 true) (by simp [live]) rfl (by simp [live, cell]) rfl]
  simp [live, cell]

theorem idle_blocks (value : U64) (env : Environment) :
    NativeWaker.pollAwait ⟨0, false⟩ (fun _ => false) (live env value 3 false) = none := by
  apply NativeWaker.pollAwait_idle <;> simp [live, cell]

theorem invalid_waker (env : Environment) :
    NativeWaker.pollAwait ⟨0, false⟩ (fun _ => true) {env with nativeHeap := []} =
      some (.error .exhausted, {env with nativeHeap := []}) := by
  apply NativeWaker.pollAwait_missing
  all_goals rfl

theorem duplicate_waker (env : Environment) :
    NativeWaker.pollAwait ⟨0, false⟩ (fun _ => true) {env with nativeHeap := [
      (0, NativeWaker.typeName, .atom "idle"), (0, NativeWaker.typeName, .atom "notified")]} =
      some (.error .exhausted, {env with nativeHeap := [
        (0, NativeWaker.typeName, .atom "idle"), (0, NativeWaker.typeName, .atom "notified")]}) := by
  simp [NativeWaker.pollAwait]

end ResourceAwait.Task
