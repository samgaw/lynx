module
public import Lynx.Term.NativeTrace.Completion
import all Lynx.Term.NativeTrace.Completion
import all Lynx.Term.NativeTrace.Blocked
import all Lynx.Term.NativeTrace.Prefix
import all Lynx.Term.NativeTrace.Serial
import all Lynx.Term.NativeTrace.Scheduled
import all Lynx.Term.Runner

/-! Finite exclusive native sections serialize through the actual scheduler,
including arbitrary finite choices and completion in either process order. -/

open Lynx Lynx.Concurrent

private theorem excludedStep {state updated : State} {pid peer : PID}
    {computation next : Result Term} {peerPoll : Environment → Option (γ × Environment)}
    {peerNext : γ → Result Term}
    {finish peerFinish : Except Exception Term → Option (Except Exception Term)}
    (ownerFirst : Bool) (root : PID) (env : Environment)
    (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice)
    (quiet : state.inTransit = []) (idle : state.timers = [])
    (own : (⟨computation, finish⟩ : Concurrent.Task Term).own state pid =
      [{event := .internal pid, state := updated, tasks := [(pid, ⟨next, finish⟩)]}])
    (blocked : peerPoll (state.nativeView peer) = none) :
    ∃ preferred' choices',
      Term.Runner.execute root env
        (.running state (pairTasks ownerFirst pid peer ⟨computation, finish⟩ ⟨.wait peerPoll peerNext, peerFinish⟩)
          none false) current preferred choices =
      Term.Runner.execute root (rootEnv root env updated)
        (.running updated (pairTasks ownerFirst pid peer ⟨next, finish⟩ ⟨.wait peerPoll peerNext, peerFinish⟩)
          none false) pid preferred' choices' := by
  have peerOwn : (⟨.wait peerPoll peerNext, peerFinish⟩ : Concurrent.Task Term).own state peer = [] := by
    simp [Concurrent.Task.own, blocked]
  have steps : (Config.running state
      (pairTasks ownerFirst pid peer ⟨computation, finish⟩ ⟨.wait peerPoll peerNext, peerFinish⟩) none false).successors =
      [(.internal pid, .running updated
        (pairTasks ownerFirst pid peer ⟨next, finish⟩ ⟨.wait peerPoll peerNext, peerFinish⟩) none false)] := by
    cases ownerFirst <;>
      simp [pairTasks, Config.successors, splits, Concurrent.Task.transitions, Concurrent.Task.deliveries,
        own, peerOwn, quiet, deliverable, deliverableFrom, State.firing, idle, firstOfEach, Transition.apply]
  exact executeSingleton root env current preferred choices steps

private theorem exclusiveRun {pid peer : PID} {peerPoll : Environment → Option (γ × Environment)}
    {peerNext : γ → Result Term} {computation : Result Term} {ownerValue peerValue : Term}
    {initial released final : Nat × List (Nat × String × Term)}
    (trace : Result.ExclusiveSteps pid peer peerPoll computation initial ownerValue released)
    (peerTrace : Result.SharedSteps peer (.wait peerPoll peerNext) released peerValue final)
    (ownerFirst ownerRoot : Bool) (root : PID) (env : Environment) (state : State)
    (distinct : peer ≠ pid) (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (quiet : state.inTransit = []) (idle : state.timers = [])
    (unlinked : ∀ process, (state.process process).links = [])
    (unwatched : ∀ process, (state.process process).monitors = [])
    (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice) :
    sharedView (Term.Runner.execute root env
      (.running state (pairTasks ownerFirst pid peer ⟨computation, capture ownerRoot⟩
        ⟨.wait peerPoll peerNext, capture (!ownerRoot)⟩) none false) current preferred choices) =
      (.ok (if ownerRoot then ownerValue else peerValue), final) := by
  induction trace generalizing env state current preferred choices with
  | done ownerValue shared =>
      exact completedShared peerTrace ownerValue ownerFirst ownerRoot root env state distinct
        counter heap quiet idle unlinked unwatched current preferred choices
  | read read body initial released ownerValue ready blocked rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      have excluded := blocked (state.nativeView peer) rfl counter heap
      obtain ⟨preferred', choices', moved⟩ := excludedStep
        (pid := pid) (peer := peer) (peerPoll := peerPoll) (peerNext := peerNext)
        (computation := .nativeGet read) (next := body) (updated := state)
        (finish := capture ownerRoot) (peerFinish := capture (!ownerRoot))
        ownerFirst root env current preferred choices quiet idle
        (by simp [Concurrent.Task.own, evaluated]) excluded
      rw [moved]
      exact ih peerTrace _ state counter heap quiet idle unlinked unwatched pid preferred' choices'
  | update read body initial middle released ownerValue ready blocked rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      have excluded := blocked (state.nativeView peer) rfl counter heap
      let setter := Result.nativeSet
        {state.nativeView pid with nativeRefCounter := middle.1, nativeHeap := middle.2} body
      let updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2}
      obtain ⟨preferred', choices', moved⟩ := excludedStep
        (pid := pid) (peer := peer) (peerPoll := peerPoll) (peerNext := peerNext)
        (computation := .nativeGet read) (next := setter) (updated := state)
        (finish := capture ownerRoot) (peerFinish := capture (!ownerRoot))
        ownerFirst root env current preferred choices quiet idle
        (by simp [Concurrent.Task.own, evaluated, setter]) excluded
      rw [moved]
      obtain ⟨preferred'', choices'', moved'⟩ := excludedStep
        (pid := pid) (peer := peer) (peerPoll := peerPoll) (peerNext := peerNext)
        (computation := setter) (next := body) (updated := updated)
        (finish := capture ownerRoot) (peerFinish := capture (!ownerRoot))
        ownerFirst root _ pid preferred' choices' quiet idle
        (by simp only [setter, Concurrent.Task.own, storeShared] <;> rfl) excluded
      rw [moved']
      exact ih peerTrace _ updated rfl rfl quiet idle unlinked unwatched pid preferred'' choices''
  | modify transition next reply initial middle released ownerValue ready blocked rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      have excluded := blocked (state.nativeView peer) rfl counter heap
      let updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2}
      obtain ⟨preferred', choices', moved⟩ := excludedStep
        (pid := pid) (peer := peer) (peerPoll := peerPoll) (peerNext := peerNext)
        (computation := .nativeModify transition next) (next := next reply) (updated := updated)
        (finish := capture ownerRoot) (peerFinish := capture (!ownerRoot))
        ownerFirst root env current preferred choices quiet idle
        (by simp only [Concurrent.Task.own, evaluated, storeShared] <;> rfl) excluded
      rw [moved]
      exact ih peerTrace _ updated rfl rfl quiet idle unlinked unwatched pid preferred' choices'
  | wait poll next reply initial middle released ownerValue ready blocked rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      have excluded := blocked (state.nativeView peer) rfl counter heap
      let updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2}
      obtain ⟨preferred', choices', moved⟩ := excludedStep
        (pid := pid) (peer := peer) (peerPoll := peerPoll) (peerNext := peerNext)
        (computation := .wait poll next) (next := next reply) (updated := updated)
        (finish := capture ownerRoot) (peerFinish := capture (!ownerRoot))
        ownerFirst root env current preferred choices quiet idle
        (by simp only [Concurrent.Task.own, evaluated, storeShared] <;> rfl) excluded
      rw [moved]
      exact ih peerTrace _ updated rfl rfl quiet idle unlinked unwatched pid preferred' choices'


private theorem initialSerial
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentValue : β) (childValue : γ) (rootFirst childFirst childSecond rootSecond : Term)
    (initial parentHeld parentReleased parentFinal childHeld childReleased childFinal : Nat × List (Nat × String × Term))
    (parentReady : ∀ env : Environment, env.currentPid = [] → env.nativeRefCounter = initial.1 →
      env.nativeHeap = initial.2 → parentPoll env =
        some (parentValue, {env with nativeRefCounter := parentHeld.1, nativeHeap := parentHeld.2}))
    (childReady : ∀ env : Environment, env.currentPid = [1] → env.nativeRefCounter = initial.1 →
      env.nativeHeap = initial.2 → childPoll env =
        some (childValue, {env with nativeRefCounter := childHeld.1, nativeHeap := childHeld.2}))
    (parent : Result.ExclusiveSteps [] [1] childPoll (parentNext parentValue) parentHeld rootFirst parentReleased)
    (childAfter : Result.SharedSteps [1] (.wait childPoll childNext) parentReleased childSecond parentFinal)
    (child : Result.ExclusiveSteps [1] [] parentPoll (childNext childValue) childHeld childFirst childReleased)
    (parentAfter : Result.SharedSteps [] (.wait parentPoll parentNext) childReleased rootSecond childFinal)
    (env : Environment) (state : State)
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (quiet : state.inTransit = []) (idle : state.timers = [])
    (unlinked : ∀ process, (state.process process).links = [])
    (unwatched : ∀ process, (state.process process).monitors = [])
    (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice) :
    let config := Config.running state
      [([], (⟨.wait parentPoll parentNext, some⟩ : Concurrent.Task Term)),
       ([1], (⟨.wait childPoll childNext, fun _ => none⟩ : Concurrent.Task Term))] none false
    sharedView (Term.Runner.execute [] (rootEnv [] env state) config current preferred choices) = (.ok rootFirst, parentFinal) ∨
    sharedView (Term.Runner.execute [] (rootEnv [] env state) config current preferred choices) = (.ok rootSecond, childFinal) := by
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
    exact exclusiveRun parent childAfter true true [] (rootEnv [] env parentUpdated) parentUpdated
      (by decide) rfl rfl quiet idle unlinked unwatched [] preferred' choices'
  · right
    rw [moved]
    simp only [Term.Runner.owner, Option.getD_some, childConfig, trackRunning]
    rw [rootEnvFrame]
    exact exclusiveRun child parentAfter false false [] (rootEnv [] env childUpdated) childUpdated
      (by decide) rfl rfl quiet idle unlinked unwatched [1] preferred' choices'

namespace Lynx.Result

/-- Two finite ready critical sections serialize under every finite scheduler
choice list. Readiness and exclusion refer to the actual operations. Both
acquisition orders retain the real root result and final shared snapshot;
external progress and infinite fairness are not assumed. -/
public theorem two_wait_serial_orders
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentValue : β) (childValue : γ) (rootFirst childFirst childSecond rootSecond : Term)
    (initial parentHeld parentReleased parentFinal childHeld childReleased childFinal :
      Nat × List (Nat × String × Term))
    (parentReady : ∀ env : Environment, env.currentPid = [] → env.nativeRefCounter = initial.1 →
      env.nativeHeap = initial.2 → parentPoll env =
        some (parentValue, {env with nativeRefCounter := parentHeld.1, nativeHeap := parentHeld.2}))
    (childReady : ∀ env : Environment, env.currentPid = [1] → env.nativeRefCounter = initial.1 →
      env.nativeHeap = initial.2 → childPoll env =
        some (childValue, {env with nativeRefCounter := childHeld.1, nativeHeap := childHeld.2}))
    (parent : ExclusiveSteps [] [1] childPoll (parentNext parentValue) parentHeld rootFirst parentReleased)
    (childAfter : SharedSteps [1] (.wait childPoll childNext) parentReleased childSecond parentFinal)
    (child : ExclusiveSteps [1] [] parentPoll (childNext childValue) childHeld childFirst childReleased)
    (parentAfter : SharedSteps [] (.wait parentPoll parentNext) childReleased rootSecond childFinal)
    (choices : List ScheduleChoice) :
    let observed :=
      (Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
        {nativeRefCounter := initial.1, nativeHeap := initial.2} choices
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) = (.ok rootFirst, parentFinal) ∨
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) = (.ok rootSecond, childFinal) := by
  change sharedView ((Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
    (startEnv initial []) choices) = (.ok rootFirst, parentFinal) ∨
    sharedView ((Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
      (startEnv initial []) choices) = (.ok rootSecond, childFinal)
  have calmLinks : ∀ pid, ((spawnedState initial []).process pid).links = [] := by
    intro pid
    by_cases a : pid = [] <;> by_cases b : pid = [1] <;>
      simp [spawnedState, startEnv, State.initial, State.spawn, State.process, State.update, a, b]
  have calmMonitors : ∀ pid, ((spawnedState initial []).process pid).monitors = [] := by
    intro pid
    by_cases a : pid = [] <;> by_cases b : pid = [1] <;>
      simp [spawnedState, startEnv, State.initial, State.spawn, State.process, State.update, a, b]
  cases choices with
  | nil =>
      rw [spawnRun (.wait parentPoll parentNext) (.wait childPoll childNext) initial []]
      exact initialSerial parentPoll parentNext childPoll childNext parentValue childValue
        rootFirst childFirst childSecond rootSecond initial parentHeld parentReleased parentFinal
        childHeld childReleased childFinal parentReady childReady parent childAfter child parentAfter
        (startEnv initial []) (spawnedState initial []) rfl rfl rfl rfl calmLinks calmMonitors [] .current []
  | cons preferred remaining =>
      rw [spawnPreferred (.wait parentPoll parentNext) (.wait childPoll childNext) initial [] preferred remaining]
      exact initialSerial parentPoll parentNext childPoll childNext parentValue childValue
        rootFirst childFirst childSecond rootSecond initial parentHeld parentReleased parentFinal
        childHeld childReleased childFinal parentReady childReady parent childAfter child parentAfter
        (startEnv initial []) (spawnedState initial []) rfl rfl rfl rfl calmLinks calmMonitors [] preferred remaining

end Lynx.Result
