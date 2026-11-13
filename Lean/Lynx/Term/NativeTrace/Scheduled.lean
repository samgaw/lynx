module
public import Lynx.Term.NativeTrace

open Lynx Lynx.Concurrent

private theorem storeShared (state : State) (pid : PID)
    (counter : Nat) (heap : List (Nat × String × Term)) (types : List String) :
    state.storeNative pid { state.nativeView pid with
      nativeRefCounter := counter, nativeHeap := heap, nativeResourceTypes := types } =
      { state with nativeRefCounter := counter, nativeHeap := heap, nativeResourceTypes := types } := by
  unfold State.storeNative State.store State.nativeView State.view State.process State.modify
  cases found : state.processes pid with
  | none => rfl
  | some process =>
    simp only [Option.getD_some, Nat.max_self]
    unfold State.update
    congr 1
    funext other
    by_cases same : other = pid
    · subst other; simp [found]
    · simp [same]

private theorem stepOwn {state : State} {before after : List (PID × Concurrent.Task α)}
    {pid : PID} {task : Concurrent.Task α} {finished : Option (Except Exception α)} {exhausted : Bool}
    {transition : Transition α} (own : transition ∈ task.own state pid) :
    Step (.running state (before ++ (pid, task) :: after) finished exhausted) transition.event
      (transition.apply before after finished exhausted) := by
  unfold Step Config.successors
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨(before, (pid, task), after), mem_splits, ?_⟩
  apply List.mem_map.mpr
  exact ⟨transition, List.mem_append_left _ own, rfl⟩

private theorem stepLocal {state updated : State} {before after : List (PID × Concurrent.Task α)}
    {pid : PID} {computation next : Result β}
    {finish : Except Exception β → Option (Except Exception α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    (own : (⟨computation, finish⟩ : Concurrent.Task α).own state pid =
      [{event := .internal pid, state := updated, tasks := [(pid, ⟨next, finish⟩)]}]) :
    Step (.running state (before ++ (pid, ⟨computation, finish⟩) :: after) finished exhausted)
      (.internal pid)
      (.running updated (before ++ (pid, ⟨next, finish⟩) :: after) finished exhausted) := by
  simpa [Transition.apply] using stepOwn (before := before) (after := after)
    (finished := finished) (exhausted := exhausted)
    (transition := {event := .internal pid, state := updated, tasks := [(pid, ⟨next, finish⟩)]})
    (by rw [own]; exact .head _)

public section

namespace Lynx.Result

/-- A finite framed native certificate follows actual scheduler successors in
an arbitrary task context. Other processes and all ordinary state remain intact;
this establishes a possible run, not an arbitrary-interleaving property. -/
theorem SharedSteps.scheduledRun {pid : PID} {computation : Result β} {value : β}
    {initial final : Nat × List (Nat × String × Term)}
    (trace : SharedSteps pid computation initial value final) (state : State)
    (before after : List (PID × Concurrent.Task α))
    (finish : Except Exception β → Option (Except Exception α))
    (finished : Option (Except Exception α)) (exhausted : Bool)
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2) :
    ∃ events, Run (.running state (before ++ (pid, ⟨computation, finish⟩) :: after) finished exhausted)
      events (.running { state with nativeRefCounter := final.1, nativeHeap := final.2 }
        (before ++ (pid, ⟨.ok value, finish⟩) :: after) finished exhausted) := by
  induction trace generalizing state with
  | done value shared =>
      simp only [← counter, ← heap]
      exact ⟨[], .refl⟩
  | read read body initial final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      obtain ⟨events, tail⟩ := ih state counter heap
      exact ⟨_, .step (stepLocal (by simp [Concurrent.Task.own, evaluated])) tail⟩
  | update read body initial middle final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      obtain ⟨events, tail⟩ := ih {state with nativeRefCounter := middle.1, nativeHeap := middle.2} rfl rfl
      refine ⟨_, .step (stepLocal (updated := state)
        (next := .nativeSet {state.nativeView pid with nativeRefCounter := middle.1, nativeHeap := middle.2} body)
        (by simp [Concurrent.Task.own, evaluated]))
        (.step (stepLocal ?_) tail)⟩
      simp [Concurrent.Task.own, storeShared] <;> rfl
  | modify transition next reply initial middle final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      obtain ⟨events, tail⟩ := ih {state with nativeRefCounter := middle.1, nativeHeap := middle.2} rfl rfl
      exact ⟨_, .step (stepLocal (by simp [Concurrent.Task.own, evaluated, storeShared] <;> rfl)) tail⟩
  | wait poll next reply initial middle final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      obtain ⟨events, tail⟩ := ih {state with nativeRefCounter := middle.1, nativeHeap := middle.2} rfl rfl
      exact ⟨_, .step (stepLocal (by simp [Concurrent.Task.own, evaluated, storeShared] <;> rfl)) tail⟩

/-- A registration/decoding prefix follows actual process steps while retaining
its residual computation. Native waits are not consumed by this certificate. -/
theorem RegisteredPrefix.scheduledRun {pid : PID} {computation residual : Result β}
    {initial final : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : RegisteredPrefix pid computation initial types residual final finalTypes) (state : State)
    (before after : List (PID × Concurrent.Task α))
    (finish : Except Exception β → Option (Except Exception α))
    (finished : Option (Except Exception α)) (exhausted : Bool)
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (available : state.nativeResourceTypes = types) :
    ∃ events, Run (.running state (before ++ (pid, ⟨computation, finish⟩) :: after) finished exhausted)
      events (.running { state with
          nativeRefCounter := final.1, nativeHeap := final.2, nativeResourceTypes := finalTypes }
        (before ++ (pid, ⟨residual, finish⟩) :: after) finished exhausted) := by
  induction trace generalizing state with
  | refl =>
      simp only [← counter, ← heap, ← available]
      exact ⟨[], .refl⟩
  | read read body initial final types finalTypes residual ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      obtain ⟨events, tail⟩ := ih state counter heap available
      exact ⟨_, .step (stepLocal (by simp [Concurrent.Task.own, evaluated])) tail⟩
  | update read body initial middle final types middleTypes finalTypes residual ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      obtain ⟨events, tail⟩ := ih {state with
        nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes} rfl rfl rfl
      refine ⟨_, .step (stepLocal (updated := state)
        (next := .nativeSet {state.nativeView pid with
          nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes} body)
        (by simp [Concurrent.Task.own, evaluated])) (.step (stepLocal ?_) tail)⟩
      simp [Concurrent.Task.own, storeShared]
  | modify transition next reply initial middle final types middleTypes finalTypes residual ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      obtain ⟨events, tail⟩ := ih {state with
        nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes} rfl rfl rfl
      exact ⟨_, .step (stepLocal (by simp [Concurrent.Task.own, evaluated, storeShared])) tail⟩

/-- Complete registration-aware native traces compose in a live task list. The
return remains an ordinary process continuation, so termination and any following
signals are handled by the shared scheduler rather than erased. -/
theorem RegisteredSteps.scheduledRun {pid : PID} {computation : Result β} {value : β}
    {initial final : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : RegisteredSteps pid computation initial types value final finalTypes) (state : State)
    (before after : List (PID × Concurrent.Task α))
    (finish : Except Exception β → Option (Except Exception α))
    (finished : Option (Except Exception α)) (exhausted : Bool)
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (available : state.nativeResourceTypes = types) :
    ∃ events, Run (.running state (before ++ (pid, ⟨computation, finish⟩) :: after) finished exhausted)
      events (.running { state with
          nativeRefCounter := final.1, nativeHeap := final.2, nativeResourceTypes := finalTypes }
        (before ++ (pid, ⟨.ok value, finish⟩) :: after) finished exhausted) := by
  induction trace generalizing state with
  | shared trace types =>
      simpa only [← available] using
        trace.scheduledRun state before after finish finished exhausted counter heap
  | read read body initial final types finalTypes value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      obtain ⟨events, tail⟩ := ih state counter heap available
      exact ⟨_, .step (stepLocal (by simp [Concurrent.Task.own, evaluated])) tail⟩
  | update read body initial middle final types middleTypes finalTypes value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      obtain ⟨events, tail⟩ := ih {state with
        nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes} rfl rfl rfl
      refine ⟨_, .step (stepLocal (updated := state)
        (next := .nativeSet {state.nativeView pid with
          nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes} body)
        (by simp [Concurrent.Task.own, evaluated])) (.step (stepLocal ?_) tail)⟩
      simp [Concurrent.Task.own, storeShared]
  | modify transition next reply initial middle final types middleTypes finalTypes value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      obtain ⟨events, tail⟩ := ih {state with
        nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes} rfl rfl rfl
      exact ⟨_, .step (stepLocal (by simp [Concurrent.Task.own, evaluated, storeShared])) tail⟩

end Lynx.Result
