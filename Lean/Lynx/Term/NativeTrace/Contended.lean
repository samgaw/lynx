module
public import Lynx.Term.NativeTrace.Prefix
import all Lynx.Term.NativeTrace.Prefix
import all Lynx.Term.NativeTrace.Serial
import all Lynx.Term.NativeTrace.Scheduled
import all Lynx.Term.Runner
import all Lynx.Concurrent.Reduction

/-! Concrete contended native execution through the shared scheduler. A blocked
peer has no own transition; its attempted selection cannot stand in for a
successful acquisition or discard the owner's later effects. -/

open Lynx Lynx.Concurrent

private theorem noOwnOwner {state : State} {pid : PID} {task : Concurrent.Task α}
    {before after : List (PID × Concurrent.Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    (distinct : (before ++ (pid, task) :: after).Pairwise (fun a b => a.1 ≠ b.1))
    (quiet : state.inTransit = []) (own : task.own state pid = [])
    {entry : Event × Config α}
    (mem : entry ∈ (Config.running state (before ++ (pid, task) :: after) finished exhausted).successors)
    (owned : Term.Runner.owner entry.1 = some pid) : False := by
  simp only [Config.successors, quiet, deliverable, deliverableFrom, List.filterMap_nil,
    List.append_nil, List.mem_append, List.mem_flatMap, List.mem_map, Prod.exists] at mem
  rcases mem with ⟨before', pid', task', after', split, moved, possible, same⟩ | ⟨timer, _, same⟩
  · simp only [Concurrent.Task.transitions, Concurrent.Task.deliveries, quiet, deliverable,
      deliverableFrom, List.filterMap_nil, List.append_nil] at possible
    cases same
    rw [ownOwner possible, Option.some.injEq] at owned
    subst pid'
    obtain ⟨rfl, rfl, rfl⟩ := split_unique distinct (mem_splits (before := before) (after := after)) split
    rw [own] at possible
    contradiction
  · cases same
    contradiction

private theorem disabledOwn {state : State} {pid : PID} {task : Concurrent.Task α}
    {before after : List (PID × Concurrent.Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    (distinct : (before ++ (pid, task) :: after).Pairwise (fun a b => a.1 ≠ b.1))
    (quiet : state.inTransit = []) (own : task.own state pid = []) :
    Term.Runner.firstWhere (.running state (before ++ (pid, task) :: after) finished exhausted)
      (Term.Runner.ordinary (.running state (before ++ (pid, task) :: after) finished exhausted) pid) = none := by
  apply List.find?_eq_none.mpr
  intro step _ picked
  have owner : Term.Runner.owner step.val.1 = some pid := by
    simp only [Term.Runner.ordinary, Bool.and_eq_true, beq_iff_eq] at picked
    exact picked.1
  exact noOwnOwner distinct quiet own step.property owner

private theorem executeSwapDisabled {config : Config α} {peer current : PID}
    {selected : Term.Runner.Successor config} (root : PID) (env : Environment)
    (blocked : Term.Runner.firstWhere config (Term.Runner.ordinary config peer) = none)
    (ready : Term.Runner.firstWhere config (Term.Runner.ordinary config current) = some selected)
    (noSignal : Term.Runner.firstWhere config (fun event => event matches .deliver _ | .bounce _) = none) :
    Term.Runner.execute root env config current (.swap peer) [] =
      Term.Runner.execute root env config current .current [] := by
  have chosen : Term.Runner.choose config current (.swap peer) [] =
      Term.Runner.choose config current .current [] := by
    simp [Term.Runner.choose, Term.Runner.requested, blocked, ready, Term.Runner.fallback]
  rw [Term.Runner.execute]
  split
  · rename_i next mem found
    have impossible := noSignal.symm.trans found
    contradiction
  · rename_i observed
    conv => rhs; rw [Term.Runner.execute]
    simp only [observed, chosen]


private def nativeAt (pid : PID) (shared : Nat × List (Nat × String × Term)) : Environment :=
  {currentPid := pid, nativeRefCounter := shared.1, nativeHeap := shared.2}

namespace Lynx.Result

/-- The selected parent-first schedule retains the failed peer acquisition,
both actual native traces, process completion and final shared state. This is
a finite schedule result; it does not assume fairness or establish all schedules. -/
public theorem two_wait_interleave_steps
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentValue : β) (childValue : γ) (rootValue childResult : Term)
    (s0 s1 s2 s3 s4 : Nat × List (Nat × String × Term)) :
    let atState := fun (pid : PID) (shared : Nat × List (Nat × String × Term)) =>
      ({ currentPid := pid, nativeRefCounter := shared.1, nativeHeap := shared.2 } : Environment)
    parentPoll (atState [] s0) = some (parentValue, atState [] s1) →
    SharedSteps [] (parentNext parentValue) s1 rootValue s2 →
    childPoll (atState [1] s1) = none →
    childPoll (atState [1] s2) = some (childValue, atState [1] s3) →
    SharedSteps [1] (childNext childValue) s3 childResult s4 →
    (Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
      {nativeRefCounter := s0.1, nativeHeap := s0.2} [.current, .swap [1]] =
      (.ok rootValue, atState [] s4) := by
  dsimp only
  intro acquired parentTrace blocked childAcquired childTrace
  change parentPoll (nativeAt [] s0) = some (parentValue, nativeAt [] s1) at acquired
  change childPoll (nativeAt [1] s1) = none at blocked
  change childPoll (nativeAt [1] s2) = some (childValue, nativeAt [1] s3) at childAcquired
  change (Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
    (startEnv s0 []) [.current, .swap [1]] = (.ok rootValue, nativeAt [] s4)
  rw [spawnPreferred (.wait parentPoll parentNext) (.wait childPoll childNext) s0 [] .current [.swap [1]]]
  let state0 := spawnedState s0 []
  let state1 := spawnedState s1 []
  let state2 := spawnedState s2 []
  let parentDone := state2.terminate [] (.atom "normal")
  let childHeld := {parentDone with nativeRefCounter := s3.1, nativeHeap := s3.2}
  let finalState := {parentDone with nativeRefCounter := s4.1, nativeHeap := s4.2}
  let allDone := finalState.terminate [1] (.atom "normal")
  let peerTask : Concurrent.Task Term := ⟨.wait childPoll childNext, fun _ => none⟩
  let ownerTask : Concurrent.Task Term := ⟨parentNext parentValue, some⟩
  let parentEnv := rootEnv [] (startEnv s0 []) state2
  have actualParent : parentPoll (state0.nativeView []) =
      some (parentValue, {state0.nativeView [] with nativeRefCounter := s1.1, nativeHeap := s1.2}) := by
    change parentPoll (nativeAt [] s0) = some (parentValue, nativeAt [] s1)
    exact acquired
  have parentOwn : (⟨.wait parentPoll parentNext, some⟩ : Concurrent.Task Term).own state0 [] =
      [{event := .internal [], state := state1, tasks := [([], ownerTask)]}] := by
    simp only [Concurrent.Task.own, actualParent, storeShared] <;> rfl
  have acquiredMove := executeOwn (before := []) (after := [([1], peerTask)])
    (finished := none) (exhausted := false)
    (transition := {event := .internal [], state := state1, tasks := [([], ownerTask)]})
    [] [] (rootEnv [] (startEnv s0 []) state0) .current [.swap [1]]
    (by simp) rfl parentOwn rfl rfl (.inl ⟨rfl, rfl⟩)
  simp [Transition.apply, trackRunning, Term.Runner.schedulingBoundary,
    Term.Runner.schedule] at acquiredMove
  change Term.Runner.execute [] (rootEnv [] (startEnv s0 []) state0)
    (.running state0 [([], (⟨.wait parentPoll parentNext, some⟩ : Concurrent.Task Term)), ([1], peerTask)] none false)
    [] .current [.swap [1]] = _
  rw [acquiredMove]
  have peerOwn : peerTask.own state1 [1] = [] := by
    simp [peerTask, Concurrent.Task.own, show state1.nativeView [1] = nativeAt [1] s1 from rfl, blocked]
  have peerBlocked := disabledOwn (before := [([], ownerTask)]) (after := [])
    (finished := none) (exhausted := false) (by simp) (show state1.inTransit = [] from rfl) peerOwn
  simp only [List.cons_append, List.nil_append] at peerBlocked
  obtain ⟨transition, own, owned, nonexpiring⟩ := sharedOne parentTrace state1 some none false rfl rfl
  have ordinary : Term.Runner.expires
      (.running state1 [([], ownerTask), ([1], peerTask)] none false) transition.event = false := by
    cases event : transition.event <;> simp_all [Term.Runner.expires, Term.Runner.owner, List.lookup, ownerTask]
  obtain ⟨selected, ownerReady, _⟩ := selectedOwn (before := []) (after := [([1], peerTask)])
    (finished := none) (exhausted := false) (by simp) (show state1.inTransit = [] from rfl) own owned ordinary
  simp only [List.nil_append] at ownerReady
  rw [executeSwapDisabled [] _ peerBlocked ownerReady (noDelivery rfl)]
  change Term.Runner.execute [] (rootEnv [] (startEnv s0 []) state1)
    (.running state1 [([], (⟨parentNext parentValue, some⟩ : Concurrent.Task Term)), ([1], peerTask)] none false)
    [] .current [] = _
  rw [sharedSerial parentTrace [] (startEnv s0 []) state1 [([1], peerTask)] some none false rfl rfl rfl]
  change Term.Runner.execute [] parentEnv
    (.running state2 [([], (⟨.ok rootValue, some⟩ : Concurrent.Task Term)), ([1], peerTask)] none false)
    [] .current [] = _
  rw [endOk [] parentEnv (by rfl)]
  change Term.Runner.execute [] (rootEnv [] parentEnv parentDone)
    (.running parentDone [([1], peerTask)] (some (.ok rootValue)) false) [] .current [] = _
  have actualChild : childPoll (parentDone.nativeView [1]) =
      some (childValue, {parentDone.nativeView [1] with nativeRefCounter := s3.1, nativeHeap := s3.2}) := by
    change childPoll (nativeAt [1] s2) = some (childValue, nativeAt [1] s3)
    exact childAcquired
  have childOwn : peerTask.own parentDone [1] =
      [{event := .internal [1], state := childHeld, tasks := [([1], (⟨childNext childValue, fun _ => none⟩ : Concurrent.Task Term))]}] := by
    simp only [peerTask, Concurrent.Task.own, actualChild, storeShared] <;> rfl
  have steps : (Config.running parentDone [([1], peerTask)] (some (.ok rootValue)) false).successors =
      [(.internal [1], .running childHeld [([1], (⟨childNext childValue, fun _ => none⟩ : Concurrent.Task Term))]
        (some (.ok rootValue)) false)] := by
    simp [Config.successors, splits, Concurrent.Task.transitions, Concurrent.Task.deliveries,
      childOwn, show parentDone.inTransit = [] from rfl, deliverable, deliverableFrom,
      State.firing, show parentDone.timers = [] from rfl, firstOfEach, Transition.apply]
  rw [executeUnique [] _ [] steps rfl rfl]
  simp only [trackRunning]
  rw [rootEnvFrame]
  rw [sharedSerial childTrace [] parentEnv childHeld [] (fun _ => none) (some (.ok rootValue)) false rfl rfl rfl]
  change Term.Runner.execute [] (rootEnv [] parentEnv finalState)
    (.running finalState [([1], (⟨.ok childResult, fun _ => none⟩ : Concurrent.Task Term))]
      (some (.ok rootValue)) false) [1] .current [] = _
  rw [endOk (state := finalState) [] _ (by rfl)]
  have stuck : (Config.running allDone ([] : List (PID × Concurrent.Task Term)) (some (.ok rootValue)) false).successors = [] := by
    rfl
  simp only [Option.orElse]
  rw [Term.Runner.execute_stuck _ _ _ stuck]
  simp [Config.outcome, nativeAt, parentEnv, rootEnv, Term.Runner.track, finalState, parentDone, state2,
    spawnedState, startEnv, State.initial, State.spawn, State.update, State.process, State.terminate,
    State.alive, State.view]

/-- Four native polls in the parent-first contended schedule. Callback equations
are required only at the actual process environments in this trace. -/
public theorem two_wait_interleave
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentRelease : Environment → Option (δ × Environment)) (parentFinish : δ → Result Term)
    (childRelease : Environment → Option (ε × Environment)) (childFinish : ε → Result Term)
    (parentValue : β) (childValue : γ) (parentReleased : δ) (childReleased : ε)
    (rootValue childResult : Term)
    (s0 s1 s2 s3 s4 : Nat × List (Nat × String × Term)) :
    let atState := fun (pid : PID) (shared : Nat × List (Nat × String × Term)) =>
      ({ currentPid := pid, nativeRefCounter := shared.1, nativeHeap := shared.2 } : Environment)
    parentPoll (atState [] s0) =
        some (parentValue, atState [] s1) →
    parentNext parentValue = .wait parentRelease parentFinish →
    childPoll (atState [1] s1) = none →
    parentRelease (atState [] s1) =
        some (parentReleased, atState [] s2) →
    parentFinish parentReleased = .ok rootValue →
    childPoll (atState [1] s2) = some (childValue, atState [1] s3) →
    childNext childValue = .wait childRelease childFinish →
    childRelease (atState [1] s3) = some (childReleased, atState [1] s4) →
    childFinish childReleased = .ok childResult →
    (Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
      { nativeRefCounter := s0.1, nativeHeap := s0.2} [.current, .swap [1]] =
      (.ok rootValue, atState [] s4) := by
  dsimp only
  intro acquired parent blocked released parentDoneEq childAcquired child childReleasedEq childDoneEq
  change parentPoll (nativeAt [] s0) = some (parentValue, nativeAt [] s1) at acquired
  change childPoll (nativeAt [1] s1) = none at blocked
  change childPoll (nativeAt [1] s2) = some (childValue, nativeAt [1] s3) at childAcquired
  change (Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
    (startEnv s0 []) [.current, .swap [1]] = (.ok rootValue, nativeAt [] s4)
  rw [spawnPreferred (.wait parentPoll parentNext) (.wait childPoll childNext) s0 [] .current [.swap [1]]]
  let state0 := spawnedState s0 []
  let state1 := spawnedState s1 []
  let state2 := spawnedState s2 []
  let parentDone := state2.terminate [] (.atom "normal")
  let childHeld := {parentDone with nativeRefCounter := s3.1, nativeHeap := s3.2}
  let finalState := {parentDone with nativeRefCounter := s4.1, nativeHeap := s4.2}
  let allDone := finalState.terminate [1] (.atom "normal")
  let peerTask : Concurrent.Task Term := ⟨.wait childPoll childNext, fun _ => none⟩
  let ownerTask : Concurrent.Task Term := ⟨parentNext parentValue, some⟩
  let parentEnv := rootEnv [] (startEnv s0 []) state2
  have actualParent : parentPoll (state0.nativeView []) =
      some (parentValue, {state0.nativeView [] with nativeRefCounter := s1.1, nativeHeap := s1.2}) := by
    change parentPoll (nativeAt [] s0) = some (parentValue, nativeAt [] s1)
    exact acquired
  have parentOwn : (⟨.wait parentPoll parentNext, some⟩ : Concurrent.Task Term).own state0 [] =
      [{event := .internal [], state := state1, tasks := [([], ownerTask)]}] := by
    simp only [Concurrent.Task.own, actualParent, storeShared] <;> rfl
  have acquiredMove := executeOwn (before := []) (after := [([1], peerTask)])
    (finished := none) (exhausted := false)
    (transition := {event := .internal [], state := state1, tasks := [([], ownerTask)]})
    [] [] (rootEnv [] (startEnv s0 []) state0) .current [.swap [1]]
    (by simp) rfl parentOwn rfl rfl (.inl ⟨rfl, rfl⟩)
  simp [Transition.apply, trackRunning, Term.Runner.schedulingBoundary,
    Term.Runner.schedule] at acquiredMove
  change Term.Runner.execute [] (rootEnv [] (startEnv s0 []) state0)
    (.running state0 [([], (⟨.wait parentPoll parentNext, some⟩ : Concurrent.Task Term)), ([1], peerTask)] none false)
    [] .current [.swap [1]] = _
  rw [acquiredMove]
  have peerOwn : peerTask.own state1 [1] = [] := by
    simp [peerTask, Concurrent.Task.own, show state1.nativeView [1] = nativeAt [1] s1 from rfl, blocked]
  have peerBlocked := disabledOwn (before := [([], ownerTask)]) (after := [])
    (finished := none) (exhausted := false) (by simp) (show state1.inTransit = [] from rfl) peerOwn
  simp only [List.cons_append, List.nil_append] at peerBlocked
  have actualRelease : parentRelease (state1.nativeView []) =
      some (parentReleased, {state1.nativeView [] with nativeRefCounter := s2.1, nativeHeap := s2.2}) := by
    change parentRelease (nativeAt [] s1) = some (parentReleased, nativeAt [] s2)
    exact released
  let transition : Transition Term := {
    event := .internal [], state := state2, tasks := [([], (⟨.ok rootValue, some⟩ : Concurrent.Task Term))]}
  have own : ownerTask.own state1 [] = [transition] := by
    simp only [ownerTask, parent, Concurrent.Task.own, actualRelease, storeShared, parentDoneEq]
    rfl
  have owned : Term.Runner.owner transition.event = some [] := rfl
  have ordinary : Term.Runner.expires
      (.running state1 [([], ownerTask), ([1], peerTask)] none false) transition.event = false := rfl
  obtain ⟨selected, ownerReady, _⟩ := selectedOwn (before := []) (after := [([1], peerTask)])
    (finished := none) (exhausted := false) (by simp) (show state1.inTransit = [] from rfl) own owned ordinary
  simp only [List.nil_append] at ownerReady
  rw [executeSwapDisabled [] _ peerBlocked ownerReady (noDelivery rfl)]
  change Term.Runner.execute [] (rootEnv [] (startEnv s0 []) state1)
    (.running state1 [([], (⟨parentNext parentValue, some⟩ : Concurrent.Task Term)), ([1], peerTask)] none false)
    [] .current [] = _
  rw [executeLocalHead (computation := parentNext parentValue) (finish := some)
    (updated := state2) (next := .ok rootValue) [] _ (by rfl) (by exact own)]
  change Term.Runner.execute [] parentEnv
    (.running state2 [([], (⟨.ok rootValue, some⟩ : Concurrent.Task Term)), ([1], peerTask)] none false)
    [] .current [] = _
  rw [endOk [] parentEnv (by rfl)]
  change Term.Runner.execute [] (rootEnv [] parentEnv parentDone)
    (.running parentDone [([1], peerTask)] (some (.ok rootValue)) false) [] .current [] = _
  have actualChild : childPoll (parentDone.nativeView [1]) =
      some (childValue, {parentDone.nativeView [1] with nativeRefCounter := s3.1, nativeHeap := s3.2}) := by
    change childPoll (nativeAt [1] s2) = some (childValue, nativeAt [1] s3)
    exact childAcquired
  have childOwn : peerTask.own parentDone [1] =
      [{event := .internal [1], state := childHeld, tasks := [([1], (⟨childNext childValue, fun _ => none⟩ : Concurrent.Task Term))]}] := by
    simp only [peerTask, Concurrent.Task.own, actualChild, storeShared] <;> rfl
  have steps : (Config.running parentDone [([1], peerTask)] (some (.ok rootValue)) false).successors =
      [(.internal [1], .running childHeld [([1], (⟨childNext childValue, fun _ => none⟩ : Concurrent.Task Term))]
        (some (.ok rootValue)) false)] := by
    simp [Config.successors, splits, Concurrent.Task.transitions, Concurrent.Task.deliveries,
      childOwn, show parentDone.inTransit = [] from rfl, deliverable, deliverableFrom,
      State.firing, show parentDone.timers = [] from rfl, firstOfEach, Transition.apply]
  rw [executeUnique [] _ [] steps rfl rfl]
  simp only [trackRunning]
  rw [rootEnvFrame]
  have actualChildRelease : childRelease (childHeld.nativeView [1]) =
      some (childReleased, {childHeld.nativeView [1] with nativeRefCounter := s4.1, nativeHeap := s4.2}) := by
    change childRelease (nativeAt [1] s3) = some (childReleased, nativeAt [1] s4)
    exact childReleasedEq
  have childReleaseOwn : (⟨childNext childValue, fun _ => none⟩ : Concurrent.Task Term).own childHeld [1] =
      [{
        event := .internal [1], state := finalState, tasks := [([1], (⟨.ok childResult, fun _ => none⟩ : Concurrent.Task Term))]}] := by
    simp only [child, Concurrent.Task.own, actualChildRelease, storeShared, childDoneEq]
    rfl
  rw [executeLocalHead (computation := childNext childValue) (finish := fun _ => none)
    (updated := finalState) (next := .ok childResult) [] _ (by rfl) childReleaseOwn]
  change Term.Runner.execute [] (rootEnv [] parentEnv finalState)
    (.running finalState [([1], (⟨.ok childResult, fun _ => none⟩ : Concurrent.Task Term))]
      (some (.ok rootValue)) false) [1] .current [] = _
  rw [endOk (state := finalState) [] _ (by rfl)]
  have stuck : (Config.running allDone ([] : List (PID × Concurrent.Task Term)) (some (.ok rootValue)) false).successors = [] := by
    rfl
  simp only [Option.orElse]
  rw [Term.Runner.execute_stuck _ _ _ stuck]
  simp [Config.outcome, nativeAt, parentEnv, rootEnv, Term.Runner.track, finalState, parentDone, state2,
    spawnedState, startEnv, State.initial, State.spawn, State.update, State.process, State.terminate,
    State.alive, State.view]

/-- Four native polls in the child-first contended schedule. The child's
completion and the root's later result remain distinct scheduler effects. -/
public theorem two_wait_interleave_child_first
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentRelease : Environment → Option (δ × Environment)) (parentFinish : δ → Result Term)
    (childRelease : Environment → Option (ε × Environment)) (childFinish : ε → Result Term)
    (parentValue : β) (childValue : γ) (parentReleased : δ) (childReleased : ε)
    (rootValue childResult : Term)
    (s0 s1 s2 s3 s4 : Nat × List (Nat × String × Term)) :
    let atState := fun (pid : PID) (shared : Nat × List (Nat × String × Term)) =>
      ({ currentPid := pid, nativeRefCounter := shared.1, nativeHeap := shared.2 } : Environment)
    childPoll (atState [1] s0) =
        some (childValue, atState [1] s1) →
    childNext childValue = .wait childRelease childFinish →
    parentPoll (atState [] s1) = none →
    childRelease (atState [1] s1) =
        some (childReleased, atState [1] s2) →
    childFinish childReleased = .ok childResult →
    parentPoll (atState [] s2) = some (parentValue, atState [] s3) →
    parentNext parentValue = .wait parentRelease parentFinish →
    parentRelease (atState [] s3) = some (parentReleased, atState [] s4) →
    parentFinish parentReleased = .ok rootValue →
    (Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
      { nativeRefCounter := s0.1, nativeHeap := s0.2} [.swap [1], .swap []] =
      (.ok rootValue, atState [] s4) := by
  dsimp only
  intro acquired child blocked released childDoneEq parentAcquired parent parentReleasedEq parentDoneEq
  change childPoll (nativeAt [1] s0) = some (childValue, nativeAt [1] s1) at acquired
  change parentPoll (nativeAt [] s1) = none at blocked
  change parentPoll (nativeAt [] s2) = some (parentValue, nativeAt [] s3) at parentAcquired
  change (Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
    (startEnv s0 []) [.swap [1], .swap []] = (.ok rootValue, nativeAt [] s4)
  rw [spawnPreferred (.wait parentPoll parentNext) (.wait childPoll childNext) s0 [] (.swap [1]) [.swap []]]
  let state0 := spawnedState s0 []
  let state1 := spawnedState s1 []
  let state2 := spawnedState s2 []
  let childDone := state2.terminate [1] (.atom "normal")
  let parentHeld := {childDone with nativeRefCounter := s3.1, nativeHeap := s3.2}
  let finalState := {childDone with nativeRefCounter := s4.1, nativeHeap := s4.2}
  let allDone := finalState.terminate [] (.atom "normal")
  let rootTask : Concurrent.Task Term := ⟨.wait parentPoll parentNext, some⟩
  let childTask : Concurrent.Task Term := ⟨.wait childPoll childNext, fun _ => none⟩
  let heldTask : Concurrent.Task Term := ⟨childNext childValue, fun _ => none⟩
  let heldEnv := rootEnv [] (startEnv s0 []) state2
  have actualChild : childPoll (state0.nativeView [1]) =
      some (childValue, {state0.nativeView [1] with nativeRefCounter := s1.1, nativeHeap := s1.2}) := by
    change childPoll (nativeAt [1] s0) = some (childValue, nativeAt [1] s1)
    exact acquired
  have childOwn : childTask.own state0 [1] =
      [{event := .internal [1], state := state1, tasks := [([1], heldTask)]}] := by
    simp only [childTask, Concurrent.Task.own, actualChild, storeShared] <;> rfl
  have acquiredMove := executeOwn (before := [([], rootTask)]) (after := [])
    (finished := none) (exhausted := false)
    (transition := {event := .internal [1], state := state1, tasks := [([1], heldTask)]})
    [] [] (rootEnv [] (startEnv s0 []) state0) (.swap [1]) [.swap []]
    (by simp) rfl childOwn rfl rfl (.inr rfl)
  simp [Transition.apply, trackRunning, Term.Runner.schedulingBoundary,
    List.lookup, Term.Runner.schedule, childTask] at acquiredMove
  change Term.Runner.execute [] (rootEnv [] (startEnv s0 []) state0)
    (.running state0 [([], rootTask), ([1], childTask)] none false) [] (.swap [1]) [.swap []] = _
  rw [acquiredMove]
  have rootOwn : rootTask.own state1 [] = [] := by
    simp [rootTask, Concurrent.Task.own, show state1.nativeView [] = nativeAt [] s1 from rfl, blocked]
  have rootBlocked := disabledOwn (before := []) (after := [([1], heldTask)])
    (finished := none) (exhausted := false) (by simp) (show state1.inTransit = [] from rfl) rootOwn
  simp only [List.nil_append] at rootBlocked
  have actualRelease : childRelease (state1.nativeView [1]) =
      some (childReleased, {state1.nativeView [1] with nativeRefCounter := s2.1, nativeHeap := s2.2}) := by
    change childRelease (nativeAt [1] s1) = some (childReleased, nativeAt [1] s2)
    exact released
  let releaseTransition : Transition Term := {
    event := .internal [1], state := state2, tasks := [([1], (⟨.ok childResult, fun _ => none⟩ : Concurrent.Task Term))]}
  have releaseOwn : heldTask.own state1 [1] = [releaseTransition] := by
    simp only [heldTask, child, Concurrent.Task.own, actualRelease, storeShared, childDoneEq] <;> rfl
  obtain ⟨selected, childReady, _⟩ := selectedOwn (before := [([], rootTask)]) (after := [])
    (finished := none) (exhausted := false) (by simp) (show state1.inTransit = [] from rfl) releaseOwn rfl rfl
  simp only [List.cons_append, List.nil_append] at childReady
  rw [executeSwapDisabled [] _ rootBlocked childReady (noDelivery rfl)]
  change Term.Runner.execute [] (rootEnv [] (startEnv s0 []) state1)
    (.running state1 [([], rootTask), ([1], heldTask)] none false) [1] .current [] = _
  have releaseMove := executeOwn (before := [([], rootTask)]) (after := [])
    (finished := none) (exhausted := false) (transition := releaseTransition)
    [] [1] (rootEnv [] (startEnv s0 []) state1) .current [] (by simp) rfl releaseOwn rfl rfl (.inl ⟨rfl, rfl⟩)
  simp [releaseTransition, Transition.apply, trackRunning, Term.Runner.schedule] at releaseMove
  rw [releaseMove]
  change Term.Runner.execute [] heldEnv
    (.running state2 [([], rootTask), ([1], (⟨.ok childResult, fun _ => none⟩ : Concurrent.Task Term))] none false)
    [1] .current [] = _
  let exitTransition : Transition Term := {
    event := .exit [1] (.atom "normal"), state := childDone, tasks := []}
  have exitOwn : (⟨.ok childResult, fun _ => none⟩ : Concurrent.Task Term).own state2 [1] = [exitTransition] := rfl
  have exitMove := executeOwn (before := [([], rootTask)]) (after := [])
    (finished := none) (exhausted := false) (transition := exitTransition)
    [] [1] heldEnv .current [] (by simp) rfl exitOwn rfl rfl (.inl ⟨rfl, rfl⟩)
  simp [exitTransition, Transition.apply, trackRunning, Term.Runner.schedulingBoundary,
    Term.Runner.schedule] at exitMove
  rw [exitMove]
  change Term.Runner.execute [] (rootEnv [] heldEnv childDone)
    (.running childDone [([], rootTask)] none false) [1] .current [] = _
  have actualParent : parentPoll (childDone.nativeView []) =
      some (parentValue, {childDone.nativeView [] with nativeRefCounter := s3.1, nativeHeap := s3.2}) := by
    change parentPoll (nativeAt [] s2) = some (parentValue, nativeAt [] s3)
    exact parentAcquired
  have parentOwn : rootTask.own childDone [] =
      [{event := .internal [], state := parentHeld, tasks := [([], (⟨parentNext parentValue, some⟩ : Concurrent.Task Term))]}] := by
    simp only [rootTask, Concurrent.Task.own, actualParent, storeShared] <;> rfl
  have steps : (Config.running childDone [([], rootTask)] none false).successors =
      [(.internal [], .running parentHeld [([], (⟨parentNext parentValue, some⟩ : Concurrent.Task Term))] none false)] := by
    simp [Config.successors, splits, Concurrent.Task.transitions, Concurrent.Task.deliveries,
      parentOwn, show childDone.inTransit = [] from rfl, deliverable, deliverableFrom,
      State.firing, show childDone.timers = [] from rfl, firstOfEach, Transition.apply]
  rw [executeUnique [] _ [1] steps rfl rfl]
  simp only [trackRunning]
  rw [rootEnvFrame]
  have actualParentRelease : parentRelease (parentHeld.nativeView []) =
      some (parentReleased, {parentHeld.nativeView [] with nativeRefCounter := s4.1, nativeHeap := s4.2}) := by
    change parentRelease (nativeAt [] s3) = some (parentReleased, nativeAt [] s4)
    exact parentReleasedEq
  have parentReleaseOwn : (⟨parentNext parentValue, some⟩ : Concurrent.Task Term).own parentHeld [] =
      [{event := .internal [], state := finalState, tasks := [([], (⟨.ok rootValue, some⟩ : Concurrent.Task Term))]}] := by
    simp only [parent, Concurrent.Task.own, actualParentRelease, storeShared, parentDoneEq] <;> rfl
  rw [executeLocalHead (computation := parentNext parentValue) (finish := some)
    (updated := finalState) (next := .ok rootValue) [] _ (by rfl) parentReleaseOwn]
  change Term.Runner.execute [] (rootEnv [] heldEnv finalState)
    (.running finalState [([], (⟨.ok rootValue, some⟩ : Concurrent.Task Term))] none false) [] .current [] = _
  rw [endOk (state := finalState) [] _ (by rfl)]
  have stuck : (Config.running allDone ([] : List (PID × Concurrent.Task Term)) (some (.ok rootValue)) false).successors = [] := by
    rfl
  simp only [Option.orElse]
  rw [Term.Runner.execute_stuck _ _ _ stuck]
  simp [Config.outcome, nativeAt, heldEnv, rootEnv, Term.Runner.track, finalState, childDone, state2,
    spawnedState, startEnv, State.initial, State.spawn, State.update, State.process, State.terminate,
    State.alive, State.view]

end Lynx.Result
