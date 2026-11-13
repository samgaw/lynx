module
public import Lynx.Term.NativeTrace.Registered
import all Lynx.Term.NativeTrace.Prefix
import all Lynx.Term.NativeTrace.Serial
import all Lynx.Term.NativeTrace.Scheduled
import all Lynx.Term.Runner

/-! Blocked native traces for every finite scheduler choice list. Execution
follows actual enabled successors; terminal blocked polls retain the shared
snapshot and never count as successful completion. -/

open Lynx Lynx.Concurrent

private theorem executeProgress {config : Config α}
    (root : PID) (env : Environment) (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice)
    (noSignal : Term.Runner.firstWhere config (fun event => event matches .deliver _ | .bounce _) = none)
    (nonempty : config.successors ≠ []) :
    ∃ event next preferred' choices', (event, next) ∈ config.successors ∧
      Term.Runner.execute root env config current preferred choices =
        Term.Runner.execute root (Term.Runner.track root env next) next
          ((Term.Runner.owner event).getD current) preferred' choices' := by
  generalize chosen : Term.Runner.choose config current preferred choices = picked
  obtain ⟨remaining, selected⟩ := picked
  cases selected with
  | none => exact False.elim (nonempty (Term.Runner.choose_none chosen))
  | some step =>
      obtain ⟨⟨event, next⟩, mem⟩ := step
      let selection := if Term.Runner.schedulingBoundary config event then
        Term.Runner.schedule remaining else (.current, remaining)
      refine ⟨event, next, selection.1, selection.2, mem, ?_⟩
      rw [Term.Runner.execute]
      split
      · rename_i next mem found
        have impossible := noSignal.symm.trans found
        contradiction
      · simp only [chosen]
        rfl

private theorem executeSingleton {config next : Config α} {pid : PID}
    (root : PID) (env : Environment) (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice)
    (steps : config.successors = [(.internal pid, next)]) :
    ∃ preferred' choices', Term.Runner.execute root env config current preferred choices =
      Term.Runner.execute root (Term.Runner.track root env next) next pid preferred' choices' := by
  have noSignal : Term.Runner.firstWhere config (fun event => event matches .deliver _ | .bounce _) = none :=
    unselectedSingle steps (by simp)
  obtain ⟨event, next', preferred', choices', mem, moved⟩ := executeProgress root env current preferred choices
    noSignal (by simp [steps])
  simp only [steps, List.mem_singleton, Prod.mk.injEq] at mem
  obtain ⟨rfl, rfl⟩ := mem
  exact ⟨preferred', choices', moved⟩

private def pairTasks (ownerFirst : Bool) (pid peer : PID) (ownerTask peerTask : Concurrent.Task α) :
    List (PID × Concurrent.Task α) :=
  if ownerFirst then [(pid, ownerTask), (peer, peerTask)] else [(peer, peerTask), (pid, ownerTask)]

private def sharedView (observed : Outcome α × Environment) : Outcome α × (Nat × List (Nat × String × Term)) :=
  (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap)

private theorem blockedRun {pid peer : PID} {peerPoll : Environment → Option (γ × Environment)}
    {computation : Result Term} {initial final : Nat × List (Nat × String × Term)}
    (trace : Result.ExclusiveBlocked pid peer peerPoll computation initial final)
    (peerNext : γ → Result Term) (root : PID) (env : Environment) (state : State) (ownerFirst : Bool)
    (finish peerFinish : Except Exception Term → Option (Except Exception Term))
    (finished : Option (Except Exception Term))
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (quiet : state.inTransit = []) (idle : state.timers = [])
    (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice) :
    sharedView (Term.Runner.execute root (rootEnv root env state)
      (.running state (pairTasks ownerFirst pid peer ⟨computation, finish⟩ ⟨.wait peerPoll peerNext, peerFinish⟩)
        finished false) current preferred choices) = (.deadlock, final) := by
  induction trace generalizing state current preferred choices with
  | blocked poll next shared stopped excluded =>
      have ownerStopped := stopped (state.nativeView pid) rfl counter heap
      have peerStopped := excluded (state.nativeView peer) rfl counter heap
      have stuck : (Config.running state
          (pairTasks ownerFirst pid peer ⟨.wait poll next, finish⟩ ⟨.wait peerPoll peerNext, peerFinish⟩)
          finished false).successors = [] := by
        cases ownerFirst <;> simp [pairTasks, Config.successors, splits, Concurrent.Task.transitions,
          Concurrent.Task.own, Concurrent.Task.deliveries, ownerStopped, peerStopped, quiet,
          deliverable, deliverableFrom, State.firing, idle, firstOfEach]
      rw [Term.Runner.execute_stuck _ _ _ stuck]
      cases ownerFirst <;> simp [sharedView, Config.outcome, pairTasks, rootEnv, Term.Runner.track, counter, heap]
  | wait poll next reply initial middle final ready excluded rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      have peerStopped := excluded (state.nativeView peer) rfl counter heap
      let updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2}
      have ownerOwn : (⟨.wait poll next, finish⟩ : Concurrent.Task Term).own state pid =
          [{event := .internal pid, state := updated, tasks := [(pid, ⟨next reply, finish⟩)]}] := by
        simp only [Concurrent.Task.own, evaluated, storeShared] <;> rfl
      have peerOwn : (⟨.wait peerPoll peerNext, peerFinish⟩ : Concurrent.Task Term).own state peer = [] := by
        simp [Concurrent.Task.own, peerStopped]
      have steps : (Config.running state
          (pairTasks ownerFirst pid peer ⟨.wait poll next, finish⟩ ⟨.wait peerPoll peerNext, peerFinish⟩)
          finished false).successors =
          [(.internal pid, .running updated
            (pairTasks ownerFirst pid peer ⟨next reply, finish⟩ ⟨.wait peerPoll peerNext, peerFinish⟩) finished false)] := by
        cases ownerFirst <;> simp [pairTasks, Config.successors, splits, Concurrent.Task.transitions,
          Concurrent.Task.deliveries, ownerOwn, peerOwn, quiet, deliverable, deliverableFrom,
          State.firing, idle, firstOfEach, Transition.apply]
      obtain ⟨preferred', choices', moved⟩ := executeSingleton root (rootEnv root env state) current preferred choices steps
      rw [moved]
      simp only [trackRunning]
      rw [rootEnvFrame]
      exact ih updated rfl rfl quiet idle pid preferred' choices'


private theorem initialBlocked
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentValue : β) (childValue : γ)
    (initial parentHeld parentFinal childHeld childFinal : Nat × List (Nat × String × Term))
    (parentReady : ∀ env : Environment, env.currentPid = [] → env.nativeRefCounter = initial.1 →
      env.nativeHeap = initial.2 → parentPoll env =
        some (parentValue, {env with nativeRefCounter := parentHeld.1, nativeHeap := parentHeld.2}))
    (childReady : ∀ env : Environment, env.currentPid = [1] → env.nativeRefCounter = initial.1 →
      env.nativeHeap = initial.2 → childPoll env =
        some (childValue, {env with nativeRefCounter := childHeld.1, nativeHeap := childHeld.2}))
    (parent : Result.ExclusiveBlocked [] [1] childPoll (parentNext parentValue) parentHeld parentFinal)
    (child : Result.ExclusiveBlocked [1] [] parentPoll (childNext childValue) childHeld childFinal)
    (env : Environment) (state : State)
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (quiet : state.inTransit = []) (idle : state.timers = [])
    (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice) :
    let config := Config.running state
      [([], (⟨.wait parentPoll parentNext, some⟩ : Concurrent.Task Term)),
       ([1], (⟨.wait childPoll childNext, fun _ => none⟩ : Concurrent.Task Term))] none false
    sharedView (Term.Runner.execute [] (rootEnv [] env state) config current preferred choices) = (.deadlock, parentFinal) ∨
    sharedView (Term.Runner.execute [] (rootEnv [] env state) config current preferred choices) = (.deadlock, childFinal) := by
  dsimp only
  let parentUpdated := {state with nativeRefCounter := parentHeld.1, nativeHeap := parentHeld.2}
  let childUpdated := {state with nativeRefCounter := childHeld.1, nativeHeap := childHeld.2}
  let initialTasks : List (PID × Concurrent.Task Term) :=
    [([], ⟨.wait parentPoll parentNext, some⟩), ([1], ⟨.wait childPoll childNext, fun _ => none⟩)]
  let parentConfig : Config Term := .running parentUpdated
    [([], ⟨parentNext parentValue, some⟩), ([1], ⟨.wait childPoll childNext, fun _ => none⟩)] none false
  let childConfig : Config Term := .running childUpdated
    [([], ⟨.wait parentPoll parentNext, some⟩), ([1], ⟨childNext childValue, fun _ => none⟩)] none false
  have evaluatedParent := parentReady (state.nativeView []) rfl counter heap
  have evaluatedChild := childReady (state.nativeView [1]) rfl counter heap
  have parentOwn : (⟨.wait parentPoll parentNext, some⟩ : Concurrent.Task Term).own state [] =
      [{event := .internal [], state := parentUpdated,
        tasks := [([], ⟨parentNext parentValue, some⟩)]}] := by
    simp only [Concurrent.Task.own, evaluatedParent, storeShared] <;> rfl
  have childOwn : (⟨.wait childPoll childNext, fun _ => none⟩ : Concurrent.Task Term).own state [1] =
      [{event := .internal [1], state := childUpdated,
        tasks := [([1], ⟨childNext childValue, fun _ => none⟩)]}] := by
    simp only [Concurrent.Task.own, evaluatedChild, storeShared] <;> rfl
  have steps : (Config.running state initialTasks none false).successors =
      [(.internal [], parentConfig), (.internal [1], childConfig)] := by
    simp [Config.successors, initialTasks, splits, Concurrent.Task.transitions, Concurrent.Task.deliveries,
      parentOwn, childOwn, quiet, deliverable, deliverableFrom, State.firing, idle, firstOfEach,
      Transition.apply, parentConfig, childConfig]
  obtain ⟨event, next, preferred', choices', mem, moved⟩ := executeProgress
    (config := .running state initialTasks none false) [] (rootEnv [] env state) current preferred choices
    (noDelivery quiet) (by simp [steps])
  simp only [steps, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at mem
  rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    rw [moved]
    simp only [Term.Runner.owner, Option.getD_some, parentConfig, trackRunning]
    rw [rootEnvFrame]
    exact blockedRun parent childNext [] env parentUpdated true some (fun _ => none) none
      rfl rfl quiet idle [] preferred' choices'
  · right
    rw [moved]
    simp only [Term.Runner.owner, Option.getD_some, childConfig, trackRunning]
    rw [rootEnvFrame]
    exact blockedRun child parentNext [] env childUpdated false (fun _ => none) some none
      rfl rfl quiet idle [1] preferred' choices'

namespace Lynx.Result

/-- Either initially ready worker can acquire first. For every finite choice
list, the actual closed execution reaches one of the certified blocked snapshots.
This proves deadlock relative to this model, not external progress or fairness. -/
public theorem two_wait_blocked_orders
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentValue : β) (childValue : γ)
    (initial parentHeld parentFinal childHeld childFinal :
      Nat × List (Nat × String × Term))
    (parentReady : ∀ env : Environment, env.currentPid = [] → env.nativeRefCounter = initial.1 →
      env.nativeHeap = initial.2 → parentPoll env =
        some (parentValue, {env with nativeRefCounter := parentHeld.1, nativeHeap := parentHeld.2}))
    (childReady : ∀ env : Environment, env.currentPid = [1] → env.nativeRefCounter = initial.1 →
      env.nativeHeap = initial.2 → childPoll env =
        some (childValue, {env with nativeRefCounter := childHeld.1, nativeHeap := childHeld.2}))
    (parent : ExclusiveBlocked [] [1] childPoll (parentNext parentValue) parentHeld parentFinal)
    (child : ExclusiveBlocked [1] [] parentPoll (childNext childValue) childHeld childFinal)
    (choices : List ScheduleChoice) :
    let observed :=
      (Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
        {nativeRefCounter := initial.1, nativeHeap := initial.2} choices
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) = (.deadlock, parentFinal) ∨
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) = (.deadlock, childFinal) := by
  change sharedView ((Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
      (startEnv initial []) choices) = (.deadlock, parentFinal) ∨
    sharedView ((Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
      (startEnv initial []) choices) = (.deadlock, childFinal)
  cases choices with
  | nil =>
      rw [spawnRun (.wait parentPoll parentNext) (.wait childPoll childNext) initial []]
      exact initialBlocked parentPoll parentNext childPoll childNext parentValue childValue
        initial parentHeld parentFinal childHeld childFinal parentReady childReady parent child
        (startEnv initial []) (spawnedState initial []) rfl rfl rfl rfl [] .current []
  | cons preferred remaining =>
      rw [spawnPreferred (.wait parentPoll parentNext) (.wait childPoll childNext) initial [] preferred remaining]
      exact initialBlocked parentPoll parentNext childPoll childNext parentValue childValue
        initial parentHeld parentFinal childHeld childFinal parentReady childReady parent child
        (startEnv initial []) (spawnedState initial []) rfl rfl rfl rfl [] preferred remaining

end Lynx.Result
