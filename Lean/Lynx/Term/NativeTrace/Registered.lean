module
public import Lynx.Term.NativeTrace.Contended
import all Lynx.Term.NativeTrace.Contended
import all Lynx.Term.NativeTrace.Prefix
import all Lynx.Term.NativeTrace.Serial
import all Lynx.Term.NativeTrace.Scheduled
import all Lynx.Term.Runner

/-! Registration-aware contention certificates for the shared executor. Registry
snapshots follow the actual local prefixes before either worker resumes its
native wait; a selected blocked worker cannot commit an acquisition. -/

open Lynx Lynx.Concurrent

private def localStart (computation : Result α) : Prop :=
  match computation with | .wait .. => False | _ => True

private theorem prefixSelectWait {pid : PID} {computation : Result β}
    {poll : Environment → Option (γ × Environment)} {next : γ → Result β}
    {initial final : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : Result.RegisteredPrefix pid computation initial types (.wait poll next) final finalTypes)
    (root current : PID) (env : Environment) (state : State)
    (before after : List (PID × Concurrent.Task α))
    (finish : Except Exception β → Option (Except Exception α))
    (finished : Option (Except Exception α)) (exhausted : Bool) (choices : List ScheduleChoice)
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (available : state.nativeResourceTypes = types) (quiet : state.inTransit = [])
    (distinct : (before ++ (pid, ⟨computation, finish⟩) :: after).Pairwise (fun a b => a.1 ≠ b.1))
    (nonwaiting : localStart computation) :
    Term.Runner.execute root (rootEnv root env state)
      (.running state (before ++ (pid, ⟨computation, finish⟩) :: after) finished exhausted) current (.swap pid) choices =
    Term.Runner.execute root (rootEnv root env {state with
        nativeRefCounter := final.1, nativeHeap := final.2, nativeResourceTypes := finalTypes})
      (.running {state with nativeRefCounter := final.1, nativeHeap := final.2, nativeResourceTypes := finalTypes}
        (before ++ (pid, ⟨.wait poll next, finish⟩) :: after) finished exhausted) pid .current choices := by
  cases trace with
  | refl => contradiction
  | read read body initial final types finalTypes residual ready rest =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      rw [executeLocalTask (updated := state) (next := body) root current _ (.swap pid) choices distinct quiet
        (by simp [Concurrent.Task.own, evaluated]) True.intro (.inr rfl), rootEnvIdempotent]
      exact prefixCurrent rest root env state before after finish finished exhausted choices
        counter heap available quiet (distinctTask distinct)
  | update read body initial middle final types middleTypes finalTypes residual ready rest =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      rw [executeLocalTask (updated := state)
        (next := .nativeSet {state.nativeView pid with
          nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes} body)
        root current _ (.swap pid) choices distinct quiet (by simp [Concurrent.Task.own, evaluated])
          True.intro (.inr rfl), rootEnvIdempotent]
      rw [executeLocalTask (updated := {state with
          nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes})
        (next := body) root pid _ .current choices (distinctTask distinct) quiet
          (by simp [Concurrent.Task.own, storeShared]) True.intro (.inl ⟨rfl, rfl⟩), rootEnvFrame]
      exact prefixCurrent rest root env _ before after finish finished exhausted choices
        rfl rfl rfl quiet (distinctTask distinct)
  | modify transition continuation reply initial middle final types middleTypes finalTypes residual ready rest =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      rw [executeLocalTask (updated := {state with
          nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes})
        (next := continuation reply) root current _ (.swap pid) choices distinct quiet
          (by simp [Concurrent.Task.own, evaluated, storeShared]) True.intro (.inr rfl), rootEnvFrame]
      exact prefixCurrent rest root env _ before after finish finished exhausted choices
        rfl rfl rfl quiet (distinctTask distinct)


private def nativeAtTypes (pid : PID) (shared : Nat × List (Nat × String × Term))
    (types : List String) : Environment :=
  {currentPid := pid, nativeRefCounter := shared.1, nativeHeap := shared.2, nativeResourceTypes := types}

private theorem registeredInterleave
    (parent child : Result Term)
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentValue : β) (childValue : γ) (rootValue childResult : Term)
    (s0 s1 s2 s3 s4 s5 s6 : Nat × List (Nat × String × Term))
    (types0 types1 types2 : List String)
    (parentPrefix : Result.RegisteredPrefix [] parent s0 types0 (.wait parentPoll parentNext) s1 types1)
    (childPrefix : Result.RegisteredPrefix [1] child s2 types1 (.wait childPoll childNext) s3 types2)
    (nonwaiting : localStart child)
    (acquired : parentPoll (nativeAtTypes [] s1 types1) = some (parentValue, nativeAtTypes [] s2 types1))
    (parentTrace : Result.SharedSteps [] (parentNext parentValue) s3 rootValue s4)
    (blocked : childPoll (nativeAtTypes [1] s3 types2) = none)
    (childAcquired : childPoll (nativeAtTypes [1] s4 types2) = some (childValue, nativeAtTypes [1] s5 types2))
    (childTrace : Result.SharedSteps [1] (childNext childValue) s5 childResult s6) :
    (Result.schedule {} child (fun _ => parent)).run (startEnv s0 types0) [.current, .swap [1]] =
      (.ok rootValue, nativeAtTypes [] s6 types2) := by
  have normalized := parentPrefix.spawnCurrent child [.swap [1]]
  change (Result.schedule {} child (fun _ => parent)).run (startEnv s0 types0) [.current, .swap [1]] =
    (Result.schedule {} child (fun _ => .wait parentPoll parentNext)).run (startEnv s1 types1) [.current, .swap [1]] at normalized
  rw [normalized, spawnPreferred (.wait parentPoll parentNext) child s1 types1 .current [.swap [1]]]
  let state0 := spawnedState s1 types1
  let heldParent := spawnedState s2 types1
  let decodedChild := spawnedState s3 types2
  let releasedParent := spawnedState s4 types2
  let parentDone := releasedParent.terminate [] (.atom "normal")
  let childHeld := {parentDone with nativeRefCounter := s5.1, nativeHeap := s5.2}
  let finalState := {parentDone with nativeRefCounter := s6.1, nativeHeap := s6.2}
  let allDone := finalState.terminate [1] (.atom "normal")
  let initialPeer : Concurrent.Task Term := ⟨child, fun _ => none⟩
  let peerTask : Concurrent.Task Term := ⟨.wait childPoll childNext, fun _ => none⟩
  let ownerTask : Concurrent.Task Term := ⟨parentNext parentValue, some⟩
  let parentEnv := rootEnv [] (startEnv s1 types1) releasedParent
  have actualParent : parentPoll (state0.nativeView []) =
      some (parentValue, {state0.nativeView [] with nativeRefCounter := s2.1, nativeHeap := s2.2}) := by
    change parentPoll (nativeAtTypes [] s1 types1) = some (parentValue, nativeAtTypes [] s2 types1)
    exact acquired
  have parentOwn : (⟨.wait parentPoll parentNext, some⟩ : Concurrent.Task Term).own state0 [] =
      [{event := .internal [], state := heldParent, tasks := [([], ownerTask)]}] := by
    simp only [Concurrent.Task.own, actualParent, storeShared] <;> rfl
  have acquiredMove := executeOwn (before := []) (after := [([1], initialPeer)])
    (finished := none) (exhausted := false)
    (transition := {event := .internal [], state := heldParent, tasks := [([], ownerTask)]})
    [] [] (rootEnv [] (startEnv s1 types1) state0) .current [.swap [1]]
    (by simp) rfl parentOwn rfl rfl (.inl ⟨rfl, rfl⟩)
  simp [Transition.apply, trackRunning, Term.Runner.schedulingBoundary, Term.Runner.schedule] at acquiredMove
  change Term.Runner.execute [] (rootEnv [] (startEnv s1 types1) state0)
    (.running state0 [([], (⟨.wait parentPoll parentNext, some⟩ : Concurrent.Task Term)), ([1], initialPeer)] none false)
    [] .current [.swap [1]] = _
  rw [acquiredMove]
  change Term.Runner.execute [] (rootEnv [] (startEnv s1 types1) heldParent)
    (.running heldParent [([], ownerTask), ([1], (⟨child, fun _ => none⟩ : Concurrent.Task Term))] none false)
    [] (.swap [1]) [] = _
  have decoded := prefixSelectWait childPrefix [] [] (startEnv s1 types1) heldParent
    [([], ownerTask)] [] (fun _ => none) none false [] rfl rfl rfl rfl (by simp) nonwaiting
  simp only [List.cons_append, List.nil_append] at decoded
  rw [decoded]
  change Term.Runner.execute [] (rootEnv [] (startEnv s1 types1) decodedChild)
    (.running decodedChild [([], ownerTask), ([1], peerTask)] none false) [1] .current [] = _
  have peerOwn : peerTask.own decodedChild [1] = [] := by
    simp [peerTask, Concurrent.Task.own,
      show decodedChild.nativeView [1] = nativeAtTypes [1] s3 types2 from rfl, blocked]
  obtain ⟨transition, own, owned, nonexpiring⟩ := sharedOne parentTrace decodedChild some none false rfl rfl
  have ordinary : Term.Runner.expires
      (.running decodedChild [([], ownerTask), ([1], peerTask)] none false) transition.event = false := by
    cases event : transition.event <;> simp_all [Term.Runner.expires, Term.Runner.owner, List.lookup, ownerTask]
  have ownerOwn : ownerTask.own decodedChild [] = [transition] := own
  have steps : (Config.running decodedChild [([], ownerTask), ([1], peerTask)] none false).successors =
      [(transition.event, transition.apply [] [([1], peerTask)] none false)] := by
    simp [Config.successors, splits, Concurrent.Task.transitions, Concurrent.Task.deliveries,
      ownerOwn, peerOwn, show decodedChild.inTransit = [] from rfl, deliverable, deliverableFrom,
      State.firing, show decodedChild.timers = [] from rfl, firstOfEach]
  have fallback := (executeUnique [] (rootEnv [] (startEnv s1 types1) decodedChild) [1] steps owned ordinary).trans
    (executeUnique [] (rootEnv [] (startEnv s1 types1) decodedChild) [] steps owned ordinary).symm
  rw [fallback]
  change Term.Runner.execute [] (rootEnv [] (startEnv s1 types1) decodedChild)
    (.running decodedChild [([], (⟨parentNext parentValue, some⟩ : Concurrent.Task Term)), ([1], peerTask)] none false)
    [] .current [] = _
  rw [sharedSerial parentTrace [] (startEnv s1 types1) decodedChild [([1], peerTask)] some none false rfl rfl rfl]
  change Term.Runner.execute [] parentEnv
    (.running releasedParent [([], (⟨.ok rootValue, some⟩ : Concurrent.Task Term)), ([1], peerTask)] none false)
    [] .current [] = _
  rw [endOk [] parentEnv (by rfl)]
  change Term.Runner.execute [] (rootEnv [] parentEnv parentDone)
    (.running parentDone [([1], peerTask)] (some (.ok rootValue)) false) [] .current [] = _
  have actualChild : childPoll (parentDone.nativeView [1]) =
      some (childValue, {parentDone.nativeView [1] with nativeRefCounter := s5.1, nativeHeap := s5.2}) := by
    change childPoll (nativeAtTypes [1] s4 types2) = some (childValue, nativeAtTypes [1] s5 types2)
    exact childAcquired
  have childOwn : peerTask.own parentDone [1] =
      [{event := .internal [1], state := childHeld, tasks := [([1], (⟨childNext childValue, fun _ => none⟩ : Concurrent.Task Term))]}] := by
    simp only [peerTask, Concurrent.Task.own, actualChild, storeShared] <;> rfl
  have childSteps : (Config.running parentDone [([1], peerTask)] (some (.ok rootValue)) false).successors =
      [(.internal [1], .running childHeld [([1], (⟨childNext childValue, fun _ => none⟩ : Concurrent.Task Term))]
        (some (.ok rootValue)) false)] := by
    simp [Config.successors, splits, Concurrent.Task.transitions, Concurrent.Task.deliveries,
      childOwn, show parentDone.inTransit = [] from rfl, deliverable, deliverableFrom,
      State.firing, show parentDone.timers = [] from rfl, firstOfEach, Transition.apply]
  rw [executeUnique [] _ [] childSteps rfl rfl]
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
  simp [Config.outcome, nativeAtTypes, parentEnv, rootEnv, Term.Runner.track, finalState,
    parentDone, releasedParent, spawnedState, startEnv, State.initial, State.spawn, State.update,
    State.process, State.terminate, State.alive, State.view]


namespace Lynx.Result

/-- A selected child read/set prefix composes with both actual native traces
in the parent-first contended schedule, retaining registry changes. -/
public theorem two_registered_interleave_steps
    (parent : Result Term) (childRead : Environment → Result Term)
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentValue : β) (childValue : γ) (rootValue childResult : Term)
    (s0 s1 s2 s3 s4 s5 s6 : Nat × List (Nat × String × Term))
    (types0 types1 types2 : List String)
    (parentPrefix : RegisteredPrefix [] parent s0 types0 (.wait parentPoll parentNext) s1 types1)
    (childPrefix : RegisteredPrefix [1] (.nativeGet childRead) s2 types1 (.wait childPoll childNext) s3 types2) :
    let atState := fun (pid : PID) (shared : Nat × List (Nat × String × Term)) (types : List String) =>
      ({ currentPid := pid, nativeRefCounter := shared.1, nativeHeap := shared.2, nativeResourceTypes := types } : Environment)
    parentPoll (atState [] s1 types1) =
      some (parentValue, atState [] s2 types1) →
    SharedSteps [] (parentNext parentValue) s3 rootValue s4 →
    childPoll (atState [1] s3 types2) = none →
    childPoll (atState [1] s4 types2) = some (childValue, atState [1] s5 types2) →
    SharedSteps [1] (childNext childValue) s5 childResult s6 →
    (Result.schedule {} (.nativeGet childRead) (fun _ => parent)).run
      { nativeRefCounter := s0.1, nativeHeap := s0.2, nativeResourceTypes := types0}
      [.current, .swap [1]] =
      (.ok rootValue, atState [] s6 types2) := by
  dsimp only
  intro acquired parentTrace blocked childAcquired childTrace
  change (Result.schedule {} (.nativeGet childRead) (fun _ => parent)).run (startEnv s0 types0)
    [.current, .swap [1]] = (.ok rootValue, nativeAtTypes [] s6 types2)
  exact registeredInterleave parent (.nativeGet childRead) parentPoll parentNext childPoll childNext
    parentValue childValue rootValue childResult s0 s1 s2 s3 s4 s5 s6 types0 types1 types2
    parentPrefix childPrefix True.intro acquired parentTrace blocked childAcquired childTrace

/-- The same concrete contended schedule with an atomic child prefix. -/
public theorem two_registered_modify_interleave_steps {δ : Type}
    (parent : Result Term) (childTransition : Environment → δ × Environment)
    (childStart : δ → Result Term)
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentValue : β) (childValue : γ) (rootValue childResult : Term)
    (s0 s1 s2 s3 s4 s5 s6 : Nat × List (Nat × String × Term))
    (types0 types1 types2 : List String)
    (parentPrefix : RegisteredPrefix [] parent s0 types0 (.wait parentPoll parentNext) s1 types1)
    (childPrefix : RegisteredPrefix [1] (.nativeModify childTransition childStart) s2 types1 (.wait childPoll childNext) s3 types2) :
    let atState := fun (pid : PID) (shared : Nat × List (Nat × String × Term)) (types : List String) =>
      ({ currentPid := pid, nativeRefCounter := shared.1, nativeHeap := shared.2, nativeResourceTypes := types } : Environment)
    parentPoll (atState [] s1 types1) =
      some (parentValue, atState [] s2 types1) →
    SharedSteps [] (parentNext parentValue) s3 rootValue s4 →
    childPoll (atState [1] s3 types2) = none →
    childPoll (atState [1] s4 types2) = some (childValue, atState [1] s5 types2) →
    SharedSteps [1] (childNext childValue) s5 childResult s6 →
    (Result.schedule {} (.nativeModify childTransition childStart) (fun _ => parent)).run
      { nativeRefCounter := s0.1, nativeHeap := s0.2, nativeResourceTypes := types0}
      [.current, .swap [1]] =
      (.ok rootValue, atState [] s6 types2) := by
  dsimp only
  intro acquired parentTrace blocked childAcquired childTrace
  change (Result.schedule {} (.nativeModify childTransition childStart) (fun _ => parent)).run (startEnv s0 types0)
    [.current, .swap [1]] = (.ok rootValue, nativeAtTypes [] s6 types2)
  exact registeredInterleave parent (.nativeModify childTransition childStart) parentPoll parentNext childPoll childNext
    parentValue childValue rootValue childResult s0 s1 s2 s3 s4 s5 s6 types0 types1 types2
    parentPrefix childPrefix True.intro acquired parentTrace blocked childAcquired childTrace

end Lynx.Result
