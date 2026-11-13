module
public import Lynx.Term.NativeTrace.Blocked
import all Lynx.Term.NativeTrace.Blocked
import all Lynx.Term.NativeTrace.Serial
import all Lynx.Term.NativeTrace.Scheduled
import all Lynx.Term.Runner

/-! Completion lemmas retain the actual scheduler's finite choice stream and
shared state, including work performed after the root process has ended. -/

open Lynx Lynx.Concurrent

private def completion (finished : Option (Except Exception Term)) : Outcome Term :=
  match finished with
  | some (.ok value) => .ok value
  | some (.error error) => .error error
  | none => .deadlock

private theorem rootView (root : PID) (env : Environment) (state : State) :
    ((rootEnv root env state).nativeRefCounter, (rootEnv root env state).nativeHeap) =
      (state.nativeRefCounter, state.nativeHeap) := by
  simp only [rootEnv, Term.Runner.track]

private theorem soleStep {state updated : State} {pid : PID} {computation next : Result Term}
    {finish : Except Exception Term → Option (Except Exception Term)}
    {finished : Option (Except Exception Term)}
    (root : PID) (env : Environment) (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice)
    (quiet : state.inTransit = []) (idle : state.timers = [])
    (own : (⟨computation, finish⟩ : Concurrent.Task Term).own state pid =
      [{event := .internal pid, state := updated, tasks := [(pid, ⟨next, finish⟩)]}]) :
    ∃ preferred' choices',
      Term.Runner.execute root env (.running state [(pid, ⟨computation, finish⟩)] finished false)
          current preferred choices =
      Term.Runner.execute root (rootEnv root env updated)
        (.running updated [(pid, ⟨next, finish⟩)] finished false) pid preferred' choices' := by
  have steps : (Config.running state [(pid, ⟨computation, finish⟩)] finished false).successors =
      [(.internal pid, .running updated [(pid, ⟨next, finish⟩)] finished false)] := by
    simp [Config.successors, splits, Concurrent.Task.transitions, Concurrent.Task.deliveries,
      own, quiet, deliverable, deliverableFrom, State.firing, idle, firstOfEach, Transition.apply]
  exact executeSingleton root env current preferred choices steps

private theorem soleDone (pid root : PID) (value : Term) (env : Environment) (state : State)
    (finish : Except Exception Term → Option (Except Exception Term))
    (finished : Option (Except Exception Term))
    (quiet : state.inTransit = []) (idle : state.timers = [])
    (unlinked : (state.process pid).links = []) (unwatched : (state.process pid).monitors = [])
    (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice) :
    sharedView (Term.Runner.execute root env
      (.running state [(pid, ⟨.ok value, finish⟩)] finished false) current preferred choices) =
      (completion ((finish (.ok value)).orElse fun _ => finished), state.nativeRefCounter, state.nativeHeap) := by
  let ended := state.terminate pid (.atom "normal")
  let stored := (finish (.ok value)).orElse fun _ => finished
  have endedQuiet : ended.inTransit = [] := by simp [ended, State.terminate, unlinked, unwatched, quiet]
  have endedIdle : ended.timers = [] := by simp [ended, State.terminate, unlinked, unwatched, idle]
  have steps : (Config.running state [(pid, ⟨.ok value, finish⟩)] finished false).successors =
      [(.exit pid (.atom "normal"), .running ended [] stored false)] := by
    simp [Config.successors, splits, Concurrent.Task.transitions, Concurrent.Task.deliveries,
      Concurrent.Task.own, Concurrent.Task.ended, quiet, deliverable, deliverableFrom,
      State.firing, idle, firstOfEach, Transition.apply, ended, stored]
  obtain ⟨event, next, preferred', choices', mem, moved⟩ := executeProgress (config := .running state [(pid, ⟨.ok value, finish⟩)] finished false)
    root env current preferred choices (noDelivery quiet) (by simp [steps])
  simp only [steps, List.mem_singleton, Prod.mk.injEq] at mem
  obtain ⟨rfl, rfl⟩ := mem
  rw [moved]
  have stuck : (Config.running ended ([] : List (PID × Concurrent.Task Term)) stored false).successors = [] := by
    simp [Config.successors, splits, endedQuiet, deliverable, deliverableFrom, State.firing, endedIdle, firstOfEach]
  rw [Term.Runner.execute_stuck _ _ _ stuck]
  simp only [sharedView, trackRunning]
  rw [rootView]
  change ((Config.running ended [] stored false).outcome, ended.nativeRefCounter, ended.nativeHeap) =
    (completion stored, state.nativeRefCounter, state.nativeHeap)
  cases storedEq : stored with
  | none => simp [storedEq, Config.outcome, completion, ended, State.terminate, unlinked, unwatched, State.update]
  | some result => cases result <;>
      simp [storedEq, Config.outcome, completion, ended, State.terminate, unlinked, unwatched, State.update]

private theorem soleShared {pid : PID} {computation : Result Term} {value : Term}
    {initial final : Nat × List (Nat × String × Term)}
    (trace : Result.SharedSteps pid computation initial value final)
    (root : PID) (env : Environment) (state : State)
    (finish : Except Exception Term → Option (Except Exception Term))
    (finished : Option (Except Exception Term))
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (quiet : state.inTransit = []) (idle : state.timers = [])
    (unlinked : (state.process pid).links = []) (unwatched : (state.process pid).monitors = [])
    (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice) :
    sharedView (Term.Runner.execute root env
      (.running state [(pid, ⟨computation, finish⟩)] finished false) current preferred choices) =
      (completion ((finish (.ok value)).orElse fun _ => finished), final) := by
  induction trace generalizing env state current preferred choices with
  | done value shared =>
      simpa only [counter, heap, Prod.eta] using
        soleDone pid root value env state finish finished quiet idle unlinked unwatched current preferred choices
  | read read body initial final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      obtain ⟨preferred', choices', moved⟩ := soleStep (pid := pid) (computation := .nativeGet read) (finish := finish) (finished := finished)
        root env current preferred choices quiet idle
        (next := body) (updated := state) (by simp [Concurrent.Task.own, evaluated])
      rw [moved]
      exact ih _ state counter heap quiet idle unlinked unwatched pid preferred' choices'
  | update read body initial middle final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      obtain ⟨preferred', choices', moved⟩ := soleStep (pid := pid) (computation := .nativeGet read) (finish := finish) (finished := finished)
        root env current preferred choices quiet idle
        (next := .nativeSet {state.nativeView pid with nativeRefCounter := middle.1, nativeHeap := middle.2} body)
        (updated := state) (by simp [Concurrent.Task.own, evaluated])
      rw [moved]
      obtain ⟨preferred'', choices'', moved'⟩ := soleStep (pid := pid) (finish := finish) (finished := finished)
        (computation := .nativeSet {state.nativeView pid with nativeRefCounter := middle.1, nativeHeap := middle.2} body)
        root _ pid preferred' choices' quiet idle
        (next := body) (updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2})
        (by simp only [Concurrent.Task.own, storeShared] <;> rfl)
      rw [moved']
      exact ih _ {state with nativeRefCounter := middle.1, nativeHeap := middle.2}
        rfl rfl quiet idle unlinked unwatched pid preferred'' choices''
  | modify transition next reply initial middle final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      obtain ⟨preferred', choices', moved⟩ := soleStep (pid := pid) (finish := finish) (finished := finished) (computation := .nativeModify transition next)
        root env current preferred choices quiet idle
        (next := next reply) (updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2})
        (by simp only [Concurrent.Task.own, evaluated, storeShared] <;> rfl)
      rw [moved]
      exact ih _ {state with nativeRefCounter := middle.1, nativeHeap := middle.2}
        rfl rfl quiet idle unlinked unwatched pid preferred' choices'
  | wait poll next reply initial middle final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      obtain ⟨preferred', choices', moved⟩ := soleStep (pid := pid) (finish := finish) (finished := finished) (computation := .wait poll next)
        root env current preferred choices quiet idle
        (next := next reply) (updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2})
        (by simp only [Concurrent.Task.own, evaluated, storeShared] <;> rfl)
      rw [moved]
      exact ih _ {state with nativeRefCounter := middle.1, nativeHeap := middle.2}
        rfl rfl quiet idle unlinked unwatched pid preferred' choices'

private theorem completedStep {state updated : State} {owner pid : PID} {ownerValue : Term}
    {computation next : Result Term}
    {finish peerFinish : Except Exception Term → Option (Except Exception Term)}
    (ownerFirst : Bool) (root : PID) (env : Environment)
    (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice)
    (quiet : state.inTransit = []) (idle : state.timers = [])
    (own : (⟨computation, peerFinish⟩ : Concurrent.Task Term).own state pid =
      [{event := .internal pid, state := updated, tasks := [(pid, ⟨next, peerFinish⟩)]}])
    (wanted : Outcome Term × (Nat × List (Nat × String × Term)))
    (sole : ∀ env current preferred choices,
      sharedView (Term.Runner.execute root env
        (.running (state.terminate owner (.atom "normal")) [(pid, ⟨computation, peerFinish⟩)]
          (finish (.ok ownerValue)) false) current preferred choices) = wanted)
    (following : ∀ env current preferred choices,
      sharedView (Term.Runner.execute root env
        (.running updated (pairTasks ownerFirst owner pid ⟨.ok ownerValue, finish⟩ ⟨next, peerFinish⟩)
          none false) current preferred choices) = wanted) :
    sharedView (Term.Runner.execute root env
      (.running state (pairTasks ownerFirst owner pid ⟨.ok ownerValue, finish⟩ ⟨computation, peerFinish⟩)
        none false) current preferred choices) = wanted := by
  let ended : Config Term := .running (state.terminate owner (.atom "normal"))
    [(pid, ⟨computation, peerFinish⟩)] (finish (.ok ownerValue)) false
  let advanced : Config Term := .running updated
    (pairTasks ownerFirst owner pid ⟨.ok ownerValue, finish⟩ ⟨next, peerFinish⟩) none false
  have ownerOwn : (⟨.ok ownerValue, finish⟩ : Concurrent.Task Term).own state owner =
      [Concurrent.Task.ended finish (.exit owner (.atom "normal")) state owner (.atom "normal") (.ok ownerValue)] := rfl
  have steps : (Config.running state
      (pairTasks ownerFirst owner pid ⟨.ok ownerValue, finish⟩ ⟨computation, peerFinish⟩) none false).successors =
      if ownerFirst then [(.exit owner (.atom "normal"), ended), (.internal pid, advanced)]
      else [(.internal pid, advanced), (.exit owner (.atom "normal"), ended)] := by
    cases ownerFirst <;>
      simp [pairTasks, Config.successors, splits, Concurrent.Task.transitions, Concurrent.Task.deliveries,
        own, ownerOwn, Concurrent.Task.ended, quiet, deliverable, deliverableFrom,
        State.firing, idle, firstOfEach, Transition.apply, ended, advanced]
  obtain ⟨event, next', preferred', choices', mem, moved⟩ := executeProgress
    (config := .running state
      (pairTasks ownerFirst owner pid ⟨.ok ownerValue, finish⟩ ⟨computation, peerFinish⟩) none false)
    root env current preferred choices (noDelivery quiet) (by cases ownerFirst <;> simp [steps])
  cases ownerFirst <;>
    simp only [steps, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at mem
  all_goals rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rw [moved]; first | exact sole _ _ _ _ | exact following _ _ _ _

private theorem terminateOtherView (state : State) (owner pid : PID) (distinct : pid ≠ owner)
    (unlinked : (state.process owner).links = []) (unwatched : (state.process owner).monitors = []) :
    (state.terminate owner (.atom "normal")).nativeView pid = state.nativeView pid := by
  simp only [State.terminate, unlinked, unwatched, Kernel.foldl_eq, List.foldl_nil]
  simp [State.nativeView, State.view, State.process, State.update, distinct]

private def capture (isRoot : Bool) : Except Exception Term → Option (Except Exception Term) :=
  if isRoot then some else fun _ => none

private theorem completedDone (owner pid root : PID) (ownerValue value : Term)
    (env : Environment) (state : State) (ownerFirst ownerRoot : Bool)
    (distinct : pid ≠ owner) (quiet : state.inTransit = []) (idle : state.timers = [])
    (unlinked : ∀ process, (state.process process).links = [])
    (unwatched : ∀ process, (state.process process).monitors = [])
    (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice) :
    sharedView (Term.Runner.execute root env
      (.running state (pairTasks ownerFirst owner pid ⟨.ok ownerValue, capture ownerRoot⟩
        ⟨.ok value, capture (!ownerRoot)⟩) none false) current preferred choices) =
      (.ok (if ownerRoot then ownerValue else value), state.nativeRefCounter, state.nativeHeap) := by
  let ownerEnded : Config Term := .running (state.terminate owner (.atom "normal"))
    [(pid, ⟨.ok value, capture (!ownerRoot)⟩)] (capture ownerRoot (.ok ownerValue)) false
  let peerEnded : Config Term := .running (state.terminate pid (.atom "normal"))
    [(owner, ⟨.ok ownerValue, capture ownerRoot⟩)] (capture (!ownerRoot) (.ok value)) false
  have steps : (Config.running state (pairTasks ownerFirst owner pid ⟨.ok ownerValue, capture ownerRoot⟩
        ⟨.ok value, capture (!ownerRoot)⟩) none false).successors =
      if ownerFirst then [(.exit owner (.atom "normal"), ownerEnded), (.exit pid (.atom "normal"), peerEnded)]
      else [(.exit pid (.atom "normal"), peerEnded), (.exit owner (.atom "normal"), ownerEnded)] := by
    cases ownerFirst <;>
      simp [pairTasks, Config.successors, splits, Concurrent.Task.transitions, Concurrent.Task.deliveries,
        Concurrent.Task.own, Concurrent.Task.ended, quiet, deliverable, deliverableFrom,
        State.firing, idle, firstOfEach, Transition.apply, ownerEnded, peerEnded]
  obtain ⟨event, next, preferred', choices', mem, moved⟩ := executeProgress
    (config := .running state (pairTasks ownerFirst owner pid ⟨.ok ownerValue, capture ownerRoot⟩
      ⟨.ok value, capture (!ownerRoot)⟩) none false)
    root env current preferred choices (noDelivery quiet) (by cases ownerFirst <;> simp [steps])
  have ownerThenPeer (env current preferred choices) :
      sharedView (Term.Runner.execute root env ownerEnded current preferred choices) =
        (.ok (if ownerRoot then ownerValue else value), state.nativeRefCounter, state.nativeHeap) := by
    have result := soleDone pid root value env (state.terminate owner (.atom "normal"))
      (capture (!ownerRoot)) (capture ownerRoot (.ok ownerValue))
      (by simp [State.terminate, unlinked, unwatched, quiet])
      (by simp [State.terminate, unlinked, unwatched, idle])
      (by simp only [State.terminate, unlinked, unwatched, Kernel.foldl_eq, List.foldl_nil]
          simpa only [State.process, State.update, ite_eq_right distinct] using unlinked pid)
      (by simp only [State.terminate, unlinked, unwatched, Kernel.foldl_eq, List.foldl_nil]
          simpa only [State.process, State.update, ite_eq_right distinct] using unwatched pid)
      current preferred choices
    cases ownerRoot <;> simpa [ownerEnded, capture, completion, State.terminate, unlinked, unwatched, State.update] using result
  have peerThenOwner (env current preferred choices) :
      sharedView (Term.Runner.execute root env peerEnded current preferred choices) =
        (.ok (if ownerRoot then ownerValue else value), state.nativeRefCounter, state.nativeHeap) := by
    have result := soleDone owner root ownerValue env (state.terminate pid (.atom "normal"))
      (capture ownerRoot) (capture (!ownerRoot) (.ok value))
      (by simp [State.terminate, unlinked, unwatched, quiet])
      (by simp [State.terminate, unlinked, unwatched, idle])
      (by simp only [State.terminate, unlinked, unwatched, Kernel.foldl_eq, List.foldl_nil]
          simpa only [State.process, State.update, ite_eq_right (Ne.symm distinct)] using unlinked owner)
      (by simp only [State.terminate, unlinked, unwatched, Kernel.foldl_eq, List.foldl_nil]
          simpa only [State.process, State.update, ite_eq_right (Ne.symm distinct)] using unwatched owner)
      current preferred choices
    cases ownerRoot <;> simpa [peerEnded, capture, completion, State.terminate, unlinked, unwatched, State.update] using result
  cases ownerFirst <;>
    simp only [steps, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at mem
  all_goals rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rw [moved]; first | exact ownerThenPeer _ _ _ _ | exact peerThenOwner _ _ _ _

private theorem soleAfterOwner {owner pid : PID} {computation : Result Term} {value : Term}
    {initial final : Nat × List (Nat × String × Term)}
    (trace : Result.SharedSteps pid computation initial value final)
    (ownerValue : Term) (ownerRoot : Bool) (root : PID) (env : Environment) (state : State)
    (distinct : pid ≠ owner) (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (quiet : state.inTransit = []) (idle : state.timers = [])
    (unlinked : ∀ process, (state.process process).links = [])
    (unwatched : ∀ process, (state.process process).monitors = [])
    (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice) :
    sharedView (Term.Runner.execute root env
      (.running (state.terminate owner (.atom "normal")) [(pid, ⟨computation, capture (!ownerRoot)⟩)]
        (capture ownerRoot (.ok ownerValue)) false) current preferred choices) =
      (.ok (if ownerRoot then ownerValue else value), final) := by
  have result := soleShared trace root env (state.terminate owner (.atom "normal"))
    (capture (!ownerRoot)) (capture ownerRoot (.ok ownerValue))
    (by simpa [State.terminate, unlinked, unwatched, State.update] using counter)
    (by simpa [State.terminate, unlinked, unwatched, State.update] using heap)
    (by simp [State.terminate, unlinked, unwatched, quiet])
    (by simp [State.terminate, unlinked, unwatched, idle])
    (by simp only [State.terminate, unlinked, unwatched, Kernel.foldl_eq, List.foldl_nil]
        simpa only [State.process, State.update, ite_eq_right distinct] using unlinked pid)
    (by simp only [State.terminate, unlinked, unwatched, Kernel.foldl_eq, List.foldl_nil]
        simpa only [State.process, State.update, ite_eq_right distinct] using unwatched pid)
    current preferred choices
  cases ownerRoot <;> simpa [capture, completion] using result

private theorem completedShared {owner pid : PID} {computation : Result Term} {value : Term}
    {initial final : Nat × List (Nat × String × Term)}
    (trace : Result.SharedSteps pid computation initial value final)
    (ownerValue : Term) (ownerFirst ownerRoot : Bool) (root : PID) (env : Environment) (state : State)
    (distinct : pid ≠ owner) (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (quiet : state.inTransit = []) (idle : state.timers = [])
    (unlinked : ∀ process, (state.process process).links = [])
    (unwatched : ∀ process, (state.process process).monitors = [])
    (current : PID) (preferred : ScheduleChoice) (choices : List ScheduleChoice) :
    sharedView (Term.Runner.execute root env
      (.running state (pairTasks ownerFirst owner pid ⟨.ok ownerValue, capture ownerRoot⟩
        ⟨computation, capture (!ownerRoot)⟩) none false) current preferred choices) =
      (.ok (if ownerRoot then ownerValue else value), final) := by
  induction trace generalizing env state current preferred choices with
  | done value shared =>
      simpa only [counter, heap, Prod.eta] using
        completedDone owner pid root ownerValue value env state ownerFirst ownerRoot distinct quiet idle
          unlinked unwatched current preferred choices
  | read read body initial final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      apply completedStep (owner := owner) (pid := pid) (ownerValue := ownerValue)
        (computation := .nativeGet read) (next := body) (updated := state)
        ownerFirst root env current preferred choices quiet idle
        (by simp [Concurrent.Task.own, evaluated])
      · intro env current preferred choices
        exact soleAfterOwner (.read read body initial final value ready rest)
          ownerValue ownerRoot root env state distinct counter heap quiet idle unlinked unwatched current preferred choices
      · intro env current preferred choices
        exact ih env state counter heap quiet idle unlinked unwatched current preferred choices
  | update read body initial middle final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      let setter := Result.nativeSet
        {state.nativeView pid with nativeRefCounter := middle.1, nativeHeap := middle.2} body
      let updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2}
      apply completedStep (owner := owner) (pid := pid) (ownerValue := ownerValue)
        (computation := .nativeGet read) (next := setter) (updated := state)
        ownerFirst root env current preferred choices quiet idle
        (by simp [Concurrent.Task.own, evaluated, setter])
      · intro env current preferred choices
        exact soleAfterOwner (.update read body initial middle final value ready rest)
          ownerValue ownerRoot root env state distinct counter heap quiet idle unlinked unwatched current preferred choices
      · intro env current preferred choices
        apply completedStep (owner := owner) (pid := pid) (ownerValue := ownerValue)
          (computation := setter) (next := body) (updated := updated)
          ownerFirst root env current preferred choices quiet idle
          (by simp only [setter, Concurrent.Task.own, storeShared] <;> rfl)
        · intro env current preferred choices
          let ended := state.terminate owner (.atom "normal")
          have sameView : ended.nativeView pid = state.nativeView pid :=
            terminateOtherView state owner pid distinct (unlinked owner) (unwatched owner)
          have endedQuiet : ended.inTransit = [] := by simp [ended, State.terminate, unlinked, unwatched, quiet]
          have endedIdle : ended.timers = [] := by simp [ended, State.terminate, unlinked, unwatched, idle]
          obtain ⟨preferred', choices', moved⟩ := soleStep
            (pid := pid) (computation := setter) (next := body) (finish := capture (!ownerRoot))
            (finished := capture ownerRoot (.ok ownerValue))
            (updated := {ended with nativeRefCounter := middle.1, nativeHeap := middle.2})
            root env current preferred choices endedQuiet endedIdle
            (by simp only [setter, ← sameView, Concurrent.Task.own, storeShared] <;> rfl)
          rw [moved]
          have result := soleShared rest root
            (rootEnv root env {ended with nativeRefCounter := middle.1, nativeHeap := middle.2})
            {ended with nativeRefCounter := middle.1, nativeHeap := middle.2}
            (capture (!ownerRoot)) (capture ownerRoot (.ok ownerValue)) rfl rfl endedQuiet endedIdle
            (by change (ended.process pid).links = []
                dsimp only [ended]
                simp only [State.terminate, unlinked, unwatched, Kernel.foldl_eq, List.foldl_nil]
                simpa only [State.process, State.update, ite_eq_right distinct] using unlinked pid)
            (by change (ended.process pid).monitors = []
                dsimp only [ended]
                simp only [State.terminate, unlinked, unwatched, Kernel.foldl_eq, List.foldl_nil]
                simpa only [State.process, State.update, ite_eq_right distinct] using unwatched pid)
            pid preferred' choices'
          cases ownerRoot <;> simpa [capture, completion] using result
        · intro env current preferred choices
          exact ih env updated rfl rfl quiet idle unlinked unwatched current preferred choices
  | modify transition next reply initial middle final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      let updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2}
      apply completedStep (owner := owner) (pid := pid) (ownerValue := ownerValue)
        (computation := .nativeModify transition next) (next := next reply) (updated := updated)
        ownerFirst root env current preferred choices quiet idle
        (by simp only [Concurrent.Task.own, evaluated, storeShared] <;> rfl)
      · intro env current preferred choices
        exact soleAfterOwner (.modify transition next reply initial middle final value ready rest)
          ownerValue ownerRoot root env state distinct counter heap quiet idle unlinked unwatched current preferred choices
      · intro env current preferred choices
        exact ih env updated rfl rfl quiet idle unlinked unwatched current preferred choices
  | wait poll next reply initial middle final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      let updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2}
      apply completedStep (owner := owner) (pid := pid) (ownerValue := ownerValue)
        (computation := .wait poll next) (next := next reply) (updated := updated)
        ownerFirst root env current preferred choices quiet idle
        (by simp only [Concurrent.Task.own, evaluated, storeShared] <;> rfl)
      · intro env current preferred choices
        exact soleAfterOwner (.wait poll next reply initial middle final value ready rest)
          ownerValue ownerRoot root env state distinct counter heap quiet idle unlinked unwatched current preferred choices
      · intro env current preferred choices
        exact ih env updated rfl rfl quiet idle unlinked unwatched current preferred choices

public section
namespace Lynx.Result

/-- A completed root and a finite native child finish for every finite choice
stream. The child's real shared writes survive root completion. This models
ready native operations; it asserts neither fairness nor external IO progress. -/
theorem two_completed_shared_choices (child : Result Term) (rootValue childValue : Term)
    (initial final : Nat × List (Nat × String × Term))
    (trace : SharedSteps [1] child initial childValue final) (choices : List ScheduleChoice) :
    let observed := (Result.schedule {} child (fun _ => .ok rootValue)).run
      {nativeRefCounter := initial.1, nativeHeap := initial.2} choices
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) = (.ok rootValue, final) := by
  change sharedView ((Result.schedule {} child (fun _ => .ok rootValue)).run (startEnv initial []) choices) = _
  cases choices with
  | nil =>
      rw [spawnRun (.ok rootValue) child initial []]
      exact completedShared trace rootValue true true [] _ (spawnedState initial []) (by decide)
        rfl rfl rfl rfl (by intro pid; by_cases a : pid = [] <;> by_cases b : pid = [1] <;>
          simp [spawnedState, startEnv, State.initial, State.spawn, State.process, State.update, a, b])
        (by intro pid; by_cases a : pid = [] <;> by_cases b : pid = [1] <;>
          simp [spawnedState, startEnv, State.initial, State.spawn, State.process, State.update, a, b]) [] .current []
  | cons preferred remaining =>
      rw [spawnPreferred (.ok rootValue) child initial [] preferred remaining]
      exact completedShared trace rootValue true true [] _ (spawnedState initial []) (by decide)
        rfl rfl rfl rfl (by intro pid; by_cases a : pid = [] <;> by_cases b : pid = [1] <;>
          simp [spawnedState, startEnv, State.initial, State.spawn, State.process, State.update, a, b])
        (by intro pid; by_cases a : pid = [] <;> by_cases b : pid = [1] <;>
          simp [spawnedState, startEnv, State.initial, State.spawn, State.process, State.update, a, b]) [] preferred remaining

end Lynx.Result
