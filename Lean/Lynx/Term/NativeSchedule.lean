module

public import Lynx.Term.NativeTrace.Scheduled
import all Lynx.Term.Runner

namespace Lynx.Term.NativeRunner

open Lynx.Concurrent

/-- Proof-local packaging of the scheduler's state and explicit choice stream.
Execution is delegated to the ordinary runner; this is not another interpreter. -/
private structure Frame extends State where
  currentPid : PID := []
  schedule : List ScheduleChoice := []

private def activate (frame : Frame) (pid : PID) : Environment := frame.toState.nativeView pid
private instance : Coe Frame Environment := ⟨fun frame => activate frame frame.currentPid⟩
private abbrev Pool := Term.Runner.Pool
private abbrev Finished := Term.Runner.Finished
/-- The parent of these two-worker certificates has already spawned its child. -/
private def save (frame : Frame) : Frame :=
  let process := frame.process frame.currentPid
  let process := if frame.currentPid = [] then { process with children := 1 } else process
  { frame with toState := frame.update frame.currentPid (some process) }
private def findReady (frame : Frame) (accept : PID → Bool) (pool : Pool α) :=
  Term.Runner.findReady frame.toState accept pool
private def findTimeout (frame : Frame) (accept : PID → Bool) (pool : Pool α) :=
  Term.Runner.findTimeout frame.toState accept pool
private def choose (pool : Pool α) (frame : Frame) (preferred : ScheduleChoice) :
    Frame × Option (PID × Bool) :=
  let (remaining, chosen) := Term.Runner.choose pool frame.toState frame.currentPid preferred frame.schedule
  ({frame with schedule := remaining}, chosen)
private def schedule (frame : Frame) : Frame × ScheduleChoice :=
  let (preferred, remaining) := Term.Runner.schedule frame.schedule
  ({frame with schedule := remaining}, preferred)
private structure Advance (before : Pool α) where
  next : Pool α
  environment : Frame
  finished : Finished α
  boundary : Bool
  exhausted : Bool
private def step (pool : Pool α) (frame : Frame) (chosen : PID) (expire : Bool) : Option (Advance pool) :=
  (Term.Runner.step pool frame.toState chosen expire).map fun advance => {
    next := advance.next
    environment := { advance.state with currentPid := chosen, schedule := frame.schedule }
    finished := advance.finished
    boundary := advance.boundary
    exhausted := advance.exhausted }
private def execute (root : PID) (frame : Frame) (pool : Pool α) (finished : Finished α)
    (preferred : ScheduleChoice) (exhausted : Bool := false) : Outcome α × Environment :=
  Term.Runner.execute root frame.toState pool finished exhausted frame.currentPid preferred frame.schedule

/-- Expose one ordinary scheduler step through the proof-local argument packaging. -/
private theorem execute_eq (root : PID) (frame : Frame) (pool : Pool α) (finished : Finished α)
    (preferred : ScheduleChoice) (exhausted : Bool) :
    execute root frame pool finished preferred exhausted =
      let (remaining, selected) := choose pool frame preferred
      match selected with
      | none => Term.Runner.stop root remaining.toState pool finished exhausted
      | some (processId, expire) =>
          match step pool remaining processId expire with
          | none => Term.Runner.stop root remaining.toState pool finished exhausted
          | some advance =>
              let (nextFrame, nextChoice) := if advance.boundary then schedule advance.environment
                else (advance.environment, ScheduleChoice.current)
              execute root nextFrame advance.next (advance.finished.orElse fun _ => finished)
                nextChoice (exhausted || advance.exhausted) := by
  unfold execute
  rw [Term.Runner.execute]
  simp only [choose, step]
  cases selected : (Term.Runner.choose pool frame.toState frame.currentPid preferred frame.schedule).2 with
  | none => simp []
  | some pair =>
    obtain ⟨processId, expire⟩ := pair
    simp only []
    cases stepped : Term.Runner.step pool frame.toState processId expire with
    | none => simp []
    | some advance =>
      simp only []
      cases boundary : advance.boundary <;> simp [boundary, schedule]

@[local simp] private theorem choose_current_ready (pool : Pool α) (state : State)
    (current : PID) (choices : List ScheduleChoice)
    (ready : Term.Runner.findReady state (· == current) pool = some current) :
    Term.Runner.choose pool state current .current choices = (choices, some (current, false)) := by
  rw [Term.Runner.choose.eq_def]
  simp only [Term.Runner.requested, ready, Option.map_some]

@[local simp] private theorem choose_swap_ready (pool : Pool α) (state : State)
    (current desired : PID) (choices : List ScheduleChoice)
    (ready : Term.Runner.findReady state (· == desired) pool = some desired) :
    Term.Runner.choose pool state current (.swap desired) choices = (choices, some (desired, false)) := by
  rw [Term.Runner.choose.eq_def]
  simp only [Term.Runner.requested, ready, Option.map_some, Option.orElse_some]

@[local simp] private theorem choose_nil (pool : Pool α) (state : State)
    (current : PID) (preferred : ScheduleChoice) :
    Term.Runner.choose pool state current preferred [] =
      match Term.Runner.requested state current pool preferred with
      | some selected => ([], some selected)
      | none => ([], (Term.Runner.runnable state current pool).orElse fun _ =>
          (Term.Runner.findTimeout state (fun _ => true) pool).map (·, true)) := by
  rw [Term.Runner.choose.eq_def]
  rfl

end Lynx.Term.NativeRunner

public section
namespace Lynx.Result

open Lynx.Concurrent
open Term.NativeRunner

section KnownNativeProcesses

attribute [local simp] Term.NativeRunner.choose_current_ready Term.NativeRunner.choose_swap_ready
  Term.NativeRunner.choose_nil Term.Runner.requested Term.Runner.runnable
  Term.Runner.findReady Term.Runner.findTimeout Term.Runner.step Term.Runner.schedule
  State.nativeView State.view State.process State.storeNative State.store State.update
  State.terminate State.modify State.deliver State.signal State.kill
  Term.NativeRunner.step Term.NativeRunner.findReady Term.NativeRunner.findTimeout
  Term.Runner.stop Term.Runner.isEmpty Term.Runner.restore

@[local simp] private theorem native_pair_order {α : Type} (parent child absent : α) :
    (fun candidate : PID => if candidate = [1] then child else if candidate = [] then parent else absent) =
      (fun candidate => if candidate = [] then parent else if candidate = [1] then child else absent) := by
  funext candidate
  by_cases root : candidate = [] <;> by_cases peer : candidate = [1] <;> simp_all

private def traceEnv (pid : PID) (saved : List (PID × ProcessState))
    (shared : Nat × List (Nat × String × Term)) (types : List String := [])
    (choices : List ScheduleChoice := []) : Term.NativeRunner.Frame :=
  { currentPid := pid, nativeRefCounter := shared.1, nativeHeap := shared.2
    nativeResourceTypes := types, schedule := choices
    processes := fun candidate =>
      (saved.find? (fun item => candidate == item.1)).map fun entry =>
        if candidate = [] then {entry.2 with children := 1} else entry.2 }

private theorem sharedSteps_left {α : Type} {computation : Result α} {value : α}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps [] computation before value after)
    (child : Result Term) (finished : Term.NativeRunner.Finished α) (types : List String := []) :
    Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [] [([1], {})] before types))
      (.parallel (.process [] computation some) (.process [1] child (fun _ => none))) finished .current =
    Term.NativeRunner.execute [] (traceEnv [] [([1], {})] after types)
      (.parallel .empty (.process [1] child (fun _ => none))) (some (.ok value, {})) .current := by
  induction trace with
  | done value shared =>
      rw [Term.NativeRunner.execute_eq]
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv]
      congr 3
      funext candidate
      repeat' split <;> simp_all
  | read read body before final value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [] [([1], {})] before types) rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      simpa +contextual [traceEnv, Term.NativeRunner.save] using ih
  | update read body before middle final value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [] [([1], {})] before types) rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      rw [Term.NativeRunner.execute_eq]
      simpa +contextual [Term.NativeRunner.choose, Term.NativeRunner.findReady, Term.NativeRunner.step,
        Term.NativeRunner.activate, Term.NativeRunner.save,
         traceEnv] using ih
  | wait poll next reply before middle final value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have polled := ready (traceEnv [] [([1], {})] before types) rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at polled
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         Term.NativeRunner.schedule, traceEnv, polled]
      simpa +contextual [traceEnv, Term.NativeRunner.save] using ih

  | modify transition next reply before middle final value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [] [([1], {})] before types) rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      simpa +contextual [traceEnv, Term.NativeRunner.save] using ih

private theorem sharedSteps_right {α : Type} {computation : Result Term} {value : Term}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps [1] computation before value after) (rootValue : α) (previous : PID) (types : List String := []) :
    Term.NativeRunner.execute [] (traceEnv previous [([1], {})] before types)
      (.parallel .empty (.process [1] computation (fun _ => none))) (some (.ok rootValue, {})) .current =
      (Outcome.ok rootValue, (traceEnv [] [] after types : Environment)) := by
  induction trace generalizing previous with
  | done value shared =>
      rw [Term.NativeRunner.execute_eq]
      by_cases same : previous = [1]
      all_goals simp +contextual [Term.NativeRunner.choose,
        Term.NativeRunner.step, Term.NativeRunner.activate,
         Term.NativeRunner.execute_eq,
         traceEnv, same, (eq_comm (a := [1]) (b := previous))]
  | read read body before final value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [1] [] before types) rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      by_cases same : previous = [1]
      all_goals
        simp +contextual [Term.NativeRunner.choose,
          Term.NativeRunner.step, Term.NativeRunner.activate,
           traceEnv, evaluated, same,
          (eq_comm (a := [1]) (b := previous))]
        simpa +contextual [traceEnv, Term.NativeRunner.activate] using ih [1]
  | update read body before middle final value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [1] [] before types) rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      by_cases same : previous = [1]
      all_goals
        simp +contextual [Term.NativeRunner.choose,
          Term.NativeRunner.step, Term.NativeRunner.activate,
           traceEnv, evaluated, same,
          (eq_comm (a := [1]) (b := previous))]
        rw [Term.NativeRunner.execute_eq]
        simpa +contextual [Term.NativeRunner.choose, Term.NativeRunner.findReady, Term.NativeRunner.step,
          Term.NativeRunner.activate, Term.NativeRunner.save,
           traceEnv] using ih [1]
  | wait poll next reply before middle final value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have polled := ready (traceEnv [1] [] before types) rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at polled
      by_cases same : previous = [1]
      all_goals
        simp +contextual [Term.NativeRunner.choose,
          Term.NativeRunner.step, Term.NativeRunner.activate,
           Term.NativeRunner.schedule, traceEnv, polled, same,
          (eq_comm (a := [1]) (b := previous))]
        simpa +contextual [traceEnv, Term.NativeRunner.activate] using ih [1]

  | modify transition next reply before middle final value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [1] [] before types) rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      by_cases same : previous = [1]
      all_goals
        simp +contextual [Term.NativeRunner.choose,
          Term.NativeRunner.step, Term.NativeRunner.activate,
           traceEnv, evaluated, same,
          (eq_comm (a := [1]) (b := previous))]
        simpa +contextual [traceEnv, Term.NativeRunner.activate] using ih [1]

private theorem registeredSteps_left {α : Type} {computation : Result α} {value : α}
    {before after : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : RegisteredSteps [] computation before types value after finalTypes)
    (child : Result Term) (finished : Term.NativeRunner.Finished α) :
    Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [] [([1], {})] before types))
      (.parallel (.process [] computation some) (.process [1] child (fun _ => none))) finished .current =
    Term.NativeRunner.execute [] (traceEnv [] [([1], {})] after finalTypes)
      (.parallel .empty (.process [1] child (fun _ => none))) (some (.ok value, {})) .current := by
  induction trace with
  | shared trace types => exact sharedSteps_left trace child finished types
  | read read body before final types finalTypes value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [] [([1], {})] before types) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      simpa +contextual [traceEnv, Term.NativeRunner.save] using ih
  | update read body before middle final types middleTypes finalTypes value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [] [([1], {})] before types) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      rw [Term.NativeRunner.execute_eq]
      simpa +contextual [Term.NativeRunner.choose, Term.NativeRunner.findReady, Term.NativeRunner.step,
        Term.NativeRunner.activate, Term.NativeRunner.save,
         traceEnv] using ih

  | modify transition next reply before middle final types middleTypes finalTypes value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [] [([1], {})] before types) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      simpa +contextual [traceEnv, Term.NativeRunner.save] using ih

private theorem registeredSteps_right {α : Type} {computation : Result Term} {value : Term}
    {before after : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : RegisteredSteps [1] computation before types value after finalTypes) (rootValue : α) (previous : PID) :
    Term.NativeRunner.execute [] (traceEnv previous [([1], {})] before types)
      (.parallel .empty (.process [1] computation (fun _ => none))) (some (.ok rootValue, {})) .current =
      (Outcome.ok rootValue, (traceEnv [] [] after finalTypes : Environment)) := by
  induction trace generalizing previous with
  | shared trace types => exact sharedSteps_right trace rootValue previous types
  | read read body before final types finalTypes value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [1] [] before types) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      by_cases same : previous = [1]
      all_goals
        simp +contextual [Term.NativeRunner.choose,
          Term.NativeRunner.step, Term.NativeRunner.activate,
           traceEnv, evaluated, same,
          (eq_comm (a := [1]) (b := previous))]
        simpa +contextual [traceEnv, Term.NativeRunner.activate] using ih [1]
  | update read body before middle final types middleTypes finalTypes value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [1] [] before types) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      by_cases same : previous = [1]
      all_goals
        simp +contextual [Term.NativeRunner.choose,
          Term.NativeRunner.step, Term.NativeRunner.activate,
           traceEnv, evaluated, same,
          (eq_comm (a := [1]) (b := previous))]
        rw [Term.NativeRunner.execute_eq]
        simpa +contextual [Term.NativeRunner.choose, Term.NativeRunner.findReady, Term.NativeRunner.step,
          Term.NativeRunner.activate, Term.NativeRunner.save,
           traceEnv] using ih [1]

  | modify transition next reply before middle final types middleTypes finalTypes value ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [1] [] before types) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      by_cases same : previous = [1]
      all_goals
        simp +contextual [Term.NativeRunner.choose,
          Term.NativeRunner.step, Term.NativeRunner.activate,
           traceEnv, evaluated, same,
          (eq_comm (a := [1]) (b := previous))]
        simpa +contextual [traceEnv, Term.NativeRunner.activate] using ih [1]

private theorem registeredPrefix_left {α : Type} {computation residual : Result α}
    {before after : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : RegisteredPrefix [] computation before types residual after finalTypes)
    (child : Result Term) (finished : Term.NativeRunner.Finished α) (choices : List ScheduleChoice) :
    Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [] [([1], {})] before types choices))
      (.parallel (.process [] computation some) (.process [1] child (fun _ => none))) finished .current =
    Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [] [([1], {})] after finalTypes choices))
      (.parallel (.process [] residual some) (.process [1] child (fun _ => none))) finished .current := by
  induction trace with
  | refl => rfl
  | read read body before final types finalTypes residual ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [] [([1], {})] before types choices) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      simpa +contextual [traceEnv, Term.NativeRunner.save] using ih
  | update read body before middle final types middleTypes finalTypes residual ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [] [([1], {})] before types choices) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      rw [Term.NativeRunner.execute_eq]
      simpa +contextual [Term.NativeRunner.choose, Term.NativeRunner.findReady, Term.NativeRunner.step,
        Term.NativeRunner.activate, Term.NativeRunner.save,
         traceEnv] using ih

  | modify transition next reply before middle final types middleTypes finalTypes residual ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [] [([1], {})] before types choices) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      simpa +contextual [traceEnv, Term.NativeRunner.save] using ih

private theorem registeredPrefix_right {α β : Type} {computation residual : Result β}
    {before after : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : RegisteredPrefix [1] computation before types residual after finalTypes)
    (parent : Result α) (finished : Term.NativeRunner.Finished α) :
    Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [1] [([], {})] before types))
      (.parallel (.process [] parent some) (.process [1] computation (fun _ => none))) finished .current =
    Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [1] [([], {})] after finalTypes))
      (.parallel (.process [] parent some) (.process [1] residual (fun _ => none))) finished .current := by
  induction trace with
  | refl => rfl
  | read read body before final types finalTypes residual ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [1] [([], {})] before types) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      simpa +contextual [traceEnv, Term.NativeRunner.save] using ih
  | update read body before middle final types middleTypes finalTypes residual ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [1] [([], {})] before types) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      rw [Term.NativeRunner.execute_eq]
      simpa +contextual [Term.NativeRunner.choose, Term.NativeRunner.findReady, Term.NativeRunner.step,
        Term.NativeRunner.activate, Term.NativeRunner.save,
         traceEnv] using ih

  | modify transition next reply before middle final types middleTypes finalTypes residual ready rest ih =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [1] [([], {})] before types) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      simpa +contextual [traceEnv, Term.NativeRunner.save] using ih

private theorem registeredPrefix_right_switch {α β γ : Type}
    {read : Environment → Result β} {poll : Environment → Option (γ × Environment)}
    {next : γ → Result β}
    {before after : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : RegisteredPrefix [1] (.nativeGet read) before types (.wait poll next) after finalTypes)
    (parent : Result α) (finished : Term.NativeRunner.Finished α) :
    Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [] [([1], {})] before types))
      (.parallel (.process [] parent some) (.process [1] (.nativeGet read) (fun _ => none))) finished (.swap [1]) =
    Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [1] [([], {})] after finalTypes))
      (.parallel (.process [] parent some) (.process [1] (.wait poll next) (fun _ => none))) finished .current := by
  cases trace with
  | read read body before final types finalTypes residual ready rest =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [1] [([], {})] before types) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      simpa +contextual [traceEnv, Term.NativeRunner.save] using registeredPrefix_right rest parent finished
  | update read body before middle final types middleTypes finalTypes residual ready rest =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [1] [([], {})] before types) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose,  Term.NativeRunner.step,
         Term.NativeRunner.save,
         traceEnv, evaluated]
      rw [Term.NativeRunner.execute_eq]
      simpa +contextual [Term.NativeRunner.choose, Term.NativeRunner.findReady, Term.NativeRunner.step,
        Term.NativeRunner.activate, Term.NativeRunner.save,
         traceEnv] using registeredPrefix_right rest parent finished

private theorem registeredPrefix_modify_right_switch {α β γ δ : Type}
    {transition : Environment → δ × Environment} {start : δ → Result β}
    {poll : Environment → Option (γ × Environment)} {next : γ → Result β}
    {before after : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : RegisteredPrefix [1] (.nativeModify transition start) before types (.wait poll next) after finalTypes)
    (parent : Result α) (finished : Term.NativeRunner.Finished α) :
    Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [] [([1], {})] before types))
      (.parallel (.process [] parent some) (.process [1] (.nativeModify transition start) (fun _ => none))) finished (.swap [1]) =
    Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [1] [([], {})] after finalTypes))
      (.parallel (.process [] parent some) (.process [1] (.wait poll next) (fun _ => none))) finished .current := by
  cases trace with
  | modify transition next reply before middle final types middleTypes finalTypes residual ready rest =>
      rw [Term.NativeRunner.execute_eq]
      have evaluated := ready (traceEnv [1] [([], {})] before types) rfl rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at evaluated
      simp +contextual [Term.NativeRunner.choose, Term.NativeRunner.step,
        Term.NativeRunner.save, traceEnv, evaluated]
      simpa +contextual [traceEnv, Term.NativeRunner.save] using registeredPrefix_right rest parent finished


private theorem sharedSteps_switch_from_blocked {α β : Type} {computation : Result α} {value : α}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps [] computation before value after)
    (poll : Environment → Option (β × Environment)) (next : β → Result Term)
    (types : List String) (finished : Term.NativeRunner.Finished α)
    (blocked : poll (traceEnv [1] [([], {})] before types) = none) :
    Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [1] [([], {})] before types))
      (.parallel (.process [] computation some) (.process [1] (.wait poll next) (fun _ => none))) finished .current =
    Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [] [([1], {})] before types))
      (.parallel (.process [] computation some) (.process [1] (.wait poll next) (fun _ => none))) finished .current := by
  cases trace with
  | done value shared =>
      conv => lhs; rw [Term.NativeRunner.execute_eq]
      conv => rhs; rw [Term.NativeRunner.execute_eq]
      simp_all [Term.NativeRunner.choose,  Term.NativeRunner.step,
        Term.NativeRunner.activate, Term.NativeRunner.save,
         traceEnv]
  | read read body before final value ready rest =>
      conv => lhs; rw [Term.NativeRunner.execute_eq]
      conv => rhs; rw [Term.NativeRunner.execute_eq]
      simp_all [Term.NativeRunner.choose,  Term.NativeRunner.step,
        Term.NativeRunner.activate, Term.NativeRunner.save,
         traceEnv]
  | update read body before middle final value ready rest =>
      conv => lhs; rw [Term.NativeRunner.execute_eq]
      conv => rhs; rw [Term.NativeRunner.execute_eq]
      simp_all [Term.NativeRunner.choose,  Term.NativeRunner.step,
        Term.NativeRunner.activate, Term.NativeRunner.save,
         traceEnv]
  | wait parentPoll parentNext reply before middle final value ready rest =>
      have polled := ready (traceEnv [] [([1], {})] before types) rfl rfl rfl
      simp +contextual [traceEnv, Term.NativeRunner.activate] at polled
      conv => lhs; rw [Term.NativeRunner.execute_eq]
      conv => rhs; rw [Term.NativeRunner.execute_eq]
      simp_all [Term.NativeRunner.choose,  Term.NativeRunner.step,
        Term.NativeRunner.activate, Term.NativeRunner.save,
         traceEnv]

  | modify transition next reply before middle final value ready rest =>
      conv => lhs; rw [Term.NativeRunner.execute_eq]
      conv => rhs; rw [Term.NativeRunner.execute_eq]
      simp_all [Term.NativeRunner.choose,  Term.NativeRunner.step,
        Term.NativeRunner.activate, Term.NativeRunner.save,
         traceEnv]

end KnownNativeProcesses

attribute [local simp] Term.NativeRunner.choose_current_ready Term.NativeRunner.choose_swap_ready
  Term.NativeRunner.choose_nil native_pair_order

private theorem choose_single_ready (pool : Term.NativeRunner.Pool α) (pid : PID)
    (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice)
    (ready : ∀ choices accept, Term.NativeRunner.findReady {env with schedule := choices} accept pool =
      if accept pid then some pid else none)
    (noTimeout : ∀ choices accept, Term.NativeRunner.findTimeout {env with schedule := choices} accept pool = none) :
    ∃ choices, Term.NativeRunner.choose pool env preferred =
      ({env with schedule := choices}, some (pid, false)) := by
  have readyCore (accept) : Term.Runner.findReady env.toState accept pool =
      if accept pid then some pid else none := ready [] accept
  have noCore (accept) : Term.Runner.findTimeout env.toState accept pool = none := noTimeout [] accept
  have runnable : Term.Runner.runnable env.toState env.currentPid pool = some (pid, false) := by
    simp only [Term.Runner.runnable, readyCore]
    cases equal : (pid == env.currentPid) <;> rfl
  have selected : ∀ choices preferred, ∃ remaining,
      Term.Runner.choose pool env.toState env.currentPid preferred choices =
        (remaining, some (pid, false)) := by
    intro choices
    induction choices with
    | nil =>
      intro preferred
      refine ⟨[], ?_⟩
      rw [Term.Runner.choose.eq_def]
      cases preferred with
      | current =>
        simp only [Term.Runner.requested, readyCore]
        cases equal : (pid == env.currentPid) <;>
          simp only [ Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.map_none, runnable, noCore,
            Option.orElse_some]
      | swap desired =>
        simp only [Term.Runner.requested, readyCore, runnable]
        cases equal : (pid == desired) <;> rfl
      | timeout desired =>
        simp only [Term.Runner.requested, noCore, runnable, Option.map_none, Option.orElse_none]
    | cons choice rest ih =>
      intro preferred
      cases preferred with
      | current =>
        cases equal : (pid == env.currentPid) with
        | false =>
          obtain ⟨remaining, selected⟩ := ih choice
          refine ⟨remaining, ?_⟩
          rw [Term.Runner.choose.eq_def]
          simpa only [Term.Runner.requested, readyCore, equal, Bool.false_eq_true, ↓reduceIte,
            Option.map_none] using selected
        | true =>
          refine ⟨choice :: rest, ?_⟩
          rw [Term.Runner.choose.eq_def]
          simp only [Term.Runner.requested, readyCore, equal, ↓reduceIte, Option.map_some]
      | swap desired =>
        refine ⟨choice :: rest, ?_⟩
        rw [Term.Runner.choose.eq_def]
        simp only [Term.Runner.requested, readyCore, runnable]
        cases equal : (pid == desired) <;> rfl
      | timeout desired =>
        refine ⟨choice :: rest, ?_⟩
        rw [Term.Runner.choose.eq_def]
        simp only [Term.Runner.requested, noCore, runnable, Option.map_none, Option.orElse_none]
  obtain ⟨remaining, selected⟩ := selected env.schedule preferred
  exact ⟨remaining, by simp only [Term.NativeRunner.choose, selected]⟩

private def sharedResult (observed : Outcome α × Environment) :
    Outcome α × (Nat × List (Nat × String × Term)) :=
  (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap)

/-- These native trace certificates describe a closed process tree without
external signals, links or monitors. General scheduler proofs remain in Concurrent. -/
private def NativeCalm (state : State) : Prop :=
  ∀ processId, (state.process processId).signal = none ∧
    (state.process processId).links = [] ∧ (state.process processId).monitors = []

@[local simp] private theorem native_store_process (state : State) (owner processId : PID)
    (counter : Nat) (heap : List (Nat × String × Term)) (types : List String) :
    (state.storeNative owner {state.nativeView owner with
      nativeRefCounter := counter, nativeHeap := heap, nativeResourceTypes := types}).process processId =
      state.process processId := by
  by_cases same : processId = owner
  · subst processId
    unfold State.storeNative State.store State.process State.update State.nativeView State.view
    cases known : state.processes owner <;> simp [State.process, known]
  · simp only [State.storeNative, State.store, State.process, State.update, same, ite_false]

local macro "native_calm" : tactic => `(tactic|
  first
  | assumption
  | (simp_all [NativeCalm, State.process, State.storeNative, State.store, State.update,
      State.terminate, State.modify, State.deliver, State.initial, State.spawnWith, State.spawn, Term.NativeRunner.save, traceEnv];
      all_goals (intro processId; (repeat' split) <;> simp_all)))

private theorem choose_empty_pair (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice) :
    Term.NativeRunner.choose (.parallel .empty .empty : Term.NativeRunner.Pool α) env preferred =
      ({env with schedule := []}, none) := by
  have emptyChoice : ∀ choices preferred,
      Term.Runner.choose (.parallel .empty .empty : Term.Runner.Pool α)
        env.toState env.currentPid preferred choices = ([], none) := by
    intro choices
    induction choices with
    | nil => intro preferred; cases preferred <;> rfl
    | cons choice rest ih =>
      intro preferred
      rw [Term.Runner.choose.eq_def]
      cases preferred <;> simpa only [Term.Runner.requested, Term.Runner.runnable,
        Term.Runner.findReady, Term.Runner.findTimeout, Option.map_none, Option.orElse_none] using ih choice
  simp only [Term.NativeRunner.choose, emptyChoice]

private theorem execute_empty_pair (root : PID) (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice)
    (finished : Term.NativeRunner.Finished α) (value : α)
    (returned : finished.map Prod.fst = some (.ok value)) :
    sharedResult (Term.NativeRunner.execute root env (.parallel .empty .empty) finished preferred) =
      (.ok value, env.nativeRefCounter, env.nativeHeap) := by
  cases finished with
  | none => simp at returned
  | some result =>
    rcases result with ⟨reply, process⟩
    simp only [Option.map_some, Option.some.injEq] at returned
    subst reply
    rw [Term.NativeRunner.execute_eq, choose_empty_pair]
    simp +contextual [  Term.Runner.stop,
      Term.Runner.isEmpty, Term.Runner.restore, sharedResult]

private def solePool (left : Bool) (pid : PID) (computation : Result β)
    (finish : Except Exception β → Option (Except Exception α)) : Term.NativeRunner.Pool α :=
  if left then .parallel (.process pid computation finish) .empty
  else .parallel .empty (.process pid computation finish)

private theorem sharedSteps_sole {α β : Type} {pid : PID} {computation : Result β} {value : β}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps pid computation before value after)
    (root : PID) (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice) (left : Bool)
    (finish : Except Exception β → Option (Except Exception α))
    (finished : Term.NativeRunner.Finished α) (rootValue : α)
    (counter : env.nativeRefCounter = before.1) (heap : env.nativeHeap = before.2)
    (returned : (finish (.ok value)).orElse (fun _ => finished.map Prod.fst) = some (.ok rootValue))
    (calm : NativeCalm env.toState := by native_calm) :
    sharedResult (Term.NativeRunner.execute root env (solePool left pid computation finish) finished preferred) =
      (.ok rootValue, after) := by
  induction trace generalizing env preferred with
  | done value shared =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2

      obtain ⟨choices, selected⟩ := choose_single_ready (solePool left pid (.ok value) finish) pid env preferred
        (by intro choices accept; cases left <;> cases accepted : accept pid <;> simp +contextual [Term.Runner.findReady,
           noSignal,  solePool, Term.NativeRunner.findReady, accepted])
        (by intro choices accept; cases left <;> simp +contextual [ Term.Runner.findTimeout,
             solePool, Term.NativeRunner.findTimeout])
      rw [Term.NativeRunner.execute_eq, selected]
      cases left <;> simp +contextual [  Term.Runner.step,
          State.terminate, noSignal, noLinks, noMonitors,solePool, Term.NativeRunner.step, ]
      all_goals
        change _ = (Outcome.ok rootValue, shared.1, shared.2)
        rw [← counter, ← heap]
        apply execute_empty_pair
        cases completed : finish (.ok value) <;> simpa +contextual [completed] using returned
  | read read body before final value ready rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2

      obtain ⟨choices, selected⟩ := choose_single_ready (solePool left pid (.nativeGet read) finish) pid env preferred
        (by intro choices accept; cases left <;> cases accepted : accept pid <;> simp +contextual [Term.Runner.findReady,
           noSignal,  solePool, Term.NativeRunner.findReady, accepted])
        (by intro choices accept; cases left <;> simp +contextual [ Term.Runner.findTimeout,
             solePool, Term.NativeRunner.findTimeout])
      have evaluated := ready (Term.NativeRunner.activate env pid) rfl counter heap
      simp only [Term.NativeRunner.activate] at evaluated
      rw [Term.NativeRunner.execute_eq, selected]
      cases left <;> simp +contextual [  Term.Runner.step,
           noSignal,  solePool, Term.NativeRunner.step, evaluated]
      all_goals apply ih <;> first | rfl | exact counter | exact heap | exact returned | native_calm
  | update read body before middle final value ready rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2

      obtain ⟨choices, selected⟩ := choose_single_ready (solePool left pid (.nativeGet read) finish) pid env preferred
        (by intro choices accept; cases left <;> cases accepted : accept pid <;> simp +contextual [Term.Runner.findReady,
           noSignal,  solePool, Term.NativeRunner.findReady, accepted])
        (by intro choices accept; cases left <;> simp +contextual [ Term.Runner.findTimeout,
             solePool, Term.NativeRunner.findTimeout])
      have evaluated := ready (Term.NativeRunner.activate env pid) rfl counter heap
      simp only [Term.NativeRunner.activate] at evaluated
      rw [Term.NativeRunner.execute_eq, selected]
      cases left <;> simp +contextual [  Term.Runner.step,
           noSignal,  solePool, Term.NativeRunner.step, evaluated]
      all_goals
        rw [Term.NativeRunner.execute_eq]
        simp +contextual [Term.Runner.findReady,  Term.Runner.step,
           noSignal,  Term.NativeRunner.choose,  Term.NativeRunner.step,
          ]
        apply ih <;> first | rfl | exact counter | exact heap | exact returned | native_calm
  | wait poll next reply before middle final value ready rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2

      have polled :
          poll (Term.NativeRunner.activate env pid) =
            some (reply, {Term.NativeRunner.activate env pid with
              nativeRefCounter := middle.1, nativeHeap := middle.2}) :=
        ready _ rfl counter heap
      simp only [Term.NativeRunner.activate] at polled
      obtain ⟨choices, selected⟩ := choose_single_ready (solePool left pid (.wait poll next) finish) pid env preferred
        (by intro choices accept; cases left <;> cases accepted : accept pid <;> simp +contextual [Term.Runner.findReady,
           noSignal,  solePool, Term.NativeRunner.findReady,  polled, accepted])
        (by intro choices accept; cases left <;> simp +contextual [ Term.Runner.findTimeout,
             solePool, Term.NativeRunner.findTimeout])
      cases choices <;> rw [Term.NativeRunner.execute_eq, selected]
      all_goals (cases left <;> simp +contextual [  Term.Runner.step,
           noSignal,  solePool, Term.NativeRunner.step, polled, Term.NativeRunner.schedule,
          ])
      all_goals apply ih <;> first | rfl | exact returned | native_calm

  | modify transition next reply before middle final value ready rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2

      obtain ⟨choices, selected⟩ := choose_single_ready (solePool left pid (.nativeModify transition next) finish) pid env preferred
        (by intro choices accept; cases left <;> cases accepted : accept pid <;> simp +contextual [Term.Runner.findReady,
           noSignal,  solePool, Term.NativeRunner.findReady, accepted])
        (by intro choices accept; cases left <;> simp +contextual [ Term.Runner.findTimeout,
             solePool, Term.NativeRunner.findTimeout])
      have evaluated := ready (Term.NativeRunner.activate env pid) rfl counter heap
      simp only [Term.NativeRunner.activate] at evaluated
      rw [Term.NativeRunner.execute_eq, selected]
      cases left <;> simp +contextual [  Term.Runner.step,
           noSignal,  solePool, Term.NativeRunner.step, evaluated]
      all_goals apply ih <;> first | rfl | exact counter | exact heap | exact returned | native_calm

private theorem choose_pair_ready (pool : Term.NativeRunner.Pool α) (env : Term.NativeRunner.Frame)
    (preferred : ScheduleChoice) (current : env.currentPid = [] ∨ env.currentPid = [1])
    (ready : ∀ accept, Term.NativeRunner.findReady env accept pool =
      if accept [] then some [] else if accept [1] then some [1] else none)
    (noTimeout : ∀ accept, Term.NativeRunner.findTimeout env accept pool = none) :
    Term.NativeRunner.choose pool env preferred = (env, some ([], false)) ∨
    Term.NativeRunner.choose pool env preferred = (env, some ([1], false)) := by
  have readyCore (accept) : Term.Runner.findReady env.toState accept pool =
      if accept [] then some [] else if accept [1] then some [1] else none := ready accept
  have noCore (accept) : Term.Runner.findTimeout env.toState accept pool = none := noTimeout accept
  have here : Term.Runner.findReady env.toState (· == env.currentPid) pool = some env.currentPid := by
    rcases current with root | child
    · simpa only [root] using (show Term.Runner.findReady env.toState (· == []) pool = some [] by
        rw [readyCore]; rfl)
    · simpa only [child] using (show Term.Runner.findReady env.toState (· == [1]) pool = some [1] by
        rw [readyCore]; rfl)
  have runnable : Term.Runner.runnable env.toState env.currentPid pool = some (env.currentPid, false) := by
    simp only [Term.Runner.runnable, here, Option.orElse_some, Option.map_some]
  have selected : ∃ pid, (pid = [] ∨ pid = [1]) ∧
      Term.Runner.requested env.toState env.currentPid pool preferred = some (pid, false) := by
    cases preferred with
    | current => exact ⟨env.currentPid, current, by simp only [Term.Runner.requested, here, Option.map_some]⟩
    | timeout desired =>
      exact ⟨env.currentPid, current, by simp only [Term.Runner.requested, noCore,
        Option.map_none, Option.orElse_none, runnable]⟩
    | swap desired =>
      by_cases root : [] = desired
      · subst desired
        refine ⟨[], Or.inl rfl, ?_⟩
        simp only [Term.Runner.requested, readyCore]
        rfl
      · by_cases child : [1] = desired
        · subst desired
          refine ⟨[1], Or.inr rfl, ?_⟩
          simp only [Term.Runner.requested, readyCore]
          rfl
        · refine ⟨env.currentPid, current, ?_⟩
          simp only [Term.Runner.requested, readyCore, beq_iff_eq, root, child, ↓reduceIte,
            Option.map_none, Option.orElse_none, runnable]
  obtain ⟨pid, member, selected⟩ := selected
  have chose : Term.NativeRunner.choose pool env preferred = (env, some (pid, false)) := by
    unfold Term.NativeRunner.choose
    rw [Term.Runner.choose.eq_def]
    simp only [selected]
  rcases member with rfl | rfl
  · exact Or.inl chose
  · exact Or.inr chose

private theorem choose_done_pair {computation : Result Term} {value : Term}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps [1] computation before value after) (rootValue : Term)
    (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice)
    (current : env.currentPid = [] ∨ env.currentPid = [1])
    (counter : env.nativeRefCounter = before.1) (heap : env.nativeHeap = before.2) :
    let pool : Term.NativeRunner.Pool Term := .parallel (.process [] (.ok rootValue) some)
      (.process [1] computation (fun _ => none))
    Term.NativeRunner.choose pool env preferred = (env, some ([], false)) ∨
    Term.NativeRunner.choose pool env preferred = (env, some ([1], false)) := by
  apply choose_pair_ready _ env preferred current
  · intro accept
    cases trace with
    | done value shared => cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, a, b]
    | read => cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, a, b]
    | update | modify => cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, a, b]
    | wait poll next reply before middle final value ready rest =>
        have polled := ready (Term.NativeRunner.activate env [1]) rfl counter heap
        simp only [Term.NativeRunner.activate] at polled
        cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, a, b, polled]
  · intro accept
    cases trace <;> simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout]

private theorem sharedSteps_pendingRoot {computation : Result Term} {value : Term}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps [1] computation before value after) (rootValue : Term)
    (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice)
    (current : env.currentPid = [] ∨ env.currentPid = [1])
    (counter : env.nativeRefCounter = before.1) (heap : env.nativeHeap = before.2)
    (calm : NativeCalm env.toState := by native_calm) :
    sharedResult (Term.NativeRunner.execute [] env
      (.parallel (.process [] (.ok rootValue) some) (.process [1] computation (fun _ => none))) none preferred) =
      (.ok rootValue, after) := by
  induction trace generalizing env preferred with
  | done value shared =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      rcases choose_done_pair (.done value shared) rootValue env preferred current counter heap with selected | selected
      all_goals rw [Term.NativeRunner.execute_eq, selected]
      · simp +contextual [Term.NativeRunner.step, Term.Runner.step, State.terminate, noSignal, noLinks, noMonitors]
        exact sharedSteps_sole (.done value shared) [] _ .current false _ _ rootValue counter heap rfl
      · simp +contextual [Term.NativeRunner.step, Term.Runner.step, State.terminate, noSignal, noLinks, noMonitors]
        exact sharedSteps_sole (.done rootValue shared) [] _ .current true _ _ rootValue counter heap rfl
  | read read body before final value ready rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have trace := SharedSteps.read read body before final value ready rest
      rcases choose_done_pair trace rootValue env preferred current counter heap with selected | selected
      all_goals rw [Term.NativeRunner.execute_eq, selected]
      · simp +contextual [Term.NativeRunner.step, Term.Runner.step, State.terminate, noSignal, noLinks, noMonitors]
        exact sharedSteps_sole trace [] _ .current false _ _ rootValue counter heap rfl
      · have evaluated := ready (Term.NativeRunner.activate env [1]) rfl counter heap
        simp only [Term.NativeRunner.activate] at evaluated
        simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,   evaluated, ]
        apply ih <;> first | exact Or.inr rfl | rfl | exact counter | exact heap | native_calm
  | update read body before middle final value ready rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have trace := SharedSteps.update read body before middle final value ready rest
      rcases choose_done_pair trace rootValue env preferred current counter heap with selected | selected
      all_goals rw [Term.NativeRunner.execute_eq, selected]
      · simp +contextual [Term.NativeRunner.step, Term.Runner.step, State.terminate, noSignal, noLinks, noMonitors]
        exact sharedSteps_sole trace [] _ .current false _ _ rootValue counter heap rfl
      · have evaluated := ready (Term.NativeRunner.activate env [1]) rfl counter heap
        simp only [Term.NativeRunner.activate] at evaluated
        simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,   evaluated, ]
        rw [Term.NativeRunner.execute_eq]
        simp +contextual [Term.NativeRunner.choose,  Term.Runner.findReady, Term.NativeRunner.step, Term.Runner.step,  noSignal,
            ]
        apply ih <;> first | exact Or.inr rfl | rfl | exact counter | exact heap | native_calm
  | wait poll next reply before middle final value ready rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have trace := SharedSteps.wait poll next reply before middle final value ready rest
      rcases choose_done_pair trace rootValue env preferred current counter heap with selected | selected
      all_goals rw [Term.NativeRunner.execute_eq, selected]
      · simp +contextual [Term.NativeRunner.step, Term.Runner.step, State.terminate, noSignal, noLinks, noMonitors]
        exact sharedSteps_sole trace [] _ .current false _ _ rootValue counter heap rfl
      · have polled := ready (Term.NativeRunner.activate env [1]) rfl counter heap
        simp only [Term.NativeRunner.activate] at polled
        cases history : env.schedule
        all_goals
          simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,
            polled, Term.NativeRunner.schedule, history]
          apply ih <;> first | exact Or.inr rfl | rfl | native_calm

  | modify transition next reply before middle final value ready rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have trace := SharedSteps.modify transition next reply before middle final value ready rest
      rcases choose_done_pair trace rootValue env preferred current counter heap with selected | selected
      all_goals rw [Term.NativeRunner.execute_eq, selected]
      · simp +contextual [Term.NativeRunner.step, Term.Runner.step, State.terminate, noSignal, noLinks, noMonitors]
        exact sharedSteps_sole trace [] _ .current false _ _ rootValue counter heap rfl
      · have evaluated := ready (Term.NativeRunner.activate env [1]) rfl counter heap
        simp only [Term.NativeRunner.activate] at evaluated
        simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,   evaluated, ]
        apply ih <;> first | exact Or.inr rfl | rfl | exact counter | exact heap | native_calm

private theorem choose_root_pair {computation : Result Term} {value : Term}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps [] computation before value after) (childValue : Term)
    (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice)
    (current : env.currentPid = [] ∨ env.currentPid = [1])
    (counter : env.nativeRefCounter = before.1) (heap : env.nativeHeap = before.2) :
    let pool : Term.NativeRunner.Pool Term := .parallel (.process [] computation some)
      (.process [1] (.ok childValue) (fun _ => none))
    Term.NativeRunner.choose pool env preferred = (env, some ([], false)) ∨
    Term.NativeRunner.choose pool env preferred = (env, some ([1], false)) := by
  apply choose_pair_ready _ env preferred current
  · intro accept
    cases trace with
    | done value shared => cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, a, b]
    | read => cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, a, b]
    | update | modify => cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, a, b]
    | wait poll next reply before middle final value ready rest =>
        have polled := ready (Term.NativeRunner.activate env []) rfl counter heap
        simp only [Term.NativeRunner.activate] at polled
        cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, a, b, polled]
  · intro accept
    cases trace <;> simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout]

private theorem sharedSteps_pendingChild {computation : Result Term} {value : Term}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps [] computation before value after) (childValue : Term)
    (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice)
    (current : env.currentPid = [] ∨ env.currentPid = [1])
    (counter : env.nativeRefCounter = before.1) (heap : env.nativeHeap = before.2)
    (calm : NativeCalm env.toState := by native_calm) :
    sharedResult (Term.NativeRunner.execute [] env
      (.parallel (.process [] computation some) (.process [1] (.ok childValue) (fun _ => none))) none preferred) =
      (.ok value, after) := by
  induction trace generalizing env preferred with
  | done value shared =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      exact sharedSteps_pendingRoot (.done childValue shared) value env preferred current counter heap
  | read read body before final value ready rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have trace := SharedSteps.read read body before final value ready rest
      rcases choose_root_pair trace childValue env preferred current counter heap with selected | selected
      all_goals rw [Term.NativeRunner.execute_eq, selected]
      · have evaluated := ready (Term.NativeRunner.activate env []) rfl counter heap
        simp only [Term.NativeRunner.activate] at evaluated
        simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,   evaluated, ]
        apply ih <;> first | exact Or.inl rfl | rfl | exact counter | exact heap | native_calm
      · simp +contextual [Term.NativeRunner.step, Term.Runner.step, State.terminate, noSignal, noLinks, noMonitors]
        exact sharedSteps_sole trace [] _ .current true _ _ value counter heap rfl
  | update read body before middle final value ready rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have trace := SharedSteps.update read body before middle final value ready rest
      rcases choose_root_pair trace childValue env preferred current counter heap with selected | selected
      all_goals rw [Term.NativeRunner.execute_eq, selected]
      · have evaluated := ready (Term.NativeRunner.activate env []) rfl counter heap
        simp only [Term.NativeRunner.activate] at evaluated
        simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,   evaluated, ]
        rw [Term.NativeRunner.execute_eq]
        simp +contextual [Term.NativeRunner.choose,  Term.Runner.findReady, Term.NativeRunner.step, Term.Runner.step,  noSignal,
            ]
        apply ih <;> first | exact Or.inl rfl | rfl | exact counter | exact heap | native_calm
      · simp +contextual [Term.NativeRunner.step, Term.Runner.step, State.terminate, noSignal, noLinks, noMonitors]
        exact sharedSteps_sole trace [] _ .current true _ _ value counter heap rfl
  | wait poll next reply before middle final value ready rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have trace := SharedSteps.wait poll next reply before middle final value ready rest
      rcases choose_root_pair trace childValue env preferred current counter heap with selected | selected
      all_goals rw [Term.NativeRunner.execute_eq, selected]
      · have polled := ready (Term.NativeRunner.activate env []) rfl counter heap
        simp only [Term.NativeRunner.activate] at polled
        cases history : env.schedule
        all_goals
          simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,
            polled, Term.NativeRunner.schedule, history]
          apply ih <;> first | exact Or.inl rfl | rfl | native_calm
      · simp +contextual [Term.NativeRunner.step, Term.Runner.step, State.terminate, noSignal, noLinks, noMonitors]
        exact sharedSteps_sole trace [] _ .current true _ _ value counter heap rfl

  | modify transition next reply before middle final value ready rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have trace := SharedSteps.modify transition next reply before middle final value ready rest
      rcases choose_root_pair trace childValue env preferred current counter heap with selected | selected
      all_goals rw [Term.NativeRunner.execute_eq, selected]
      · have evaluated := ready (Term.NativeRunner.activate env []) rfl counter heap
        simp only [Term.NativeRunner.activate] at evaluated
        simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,   evaluated, ]
        apply ih <;> first | exact Or.inl rfl | rfl | exact counter | exact heap | native_calm
      · simp +contextual [Term.NativeRunner.step, Term.Runner.step, State.terminate, noSignal, noLinks, noMonitors]
        exact sharedSteps_sole trace [] _ .current true _ _ value counter heap rfl

private theorem choose_none_ready (pool : Term.NativeRunner.Pool α) (env : Term.NativeRunner.Frame)
    (preferred : ScheduleChoice)
    (ready : ∀ choices accept, Term.NativeRunner.findReady {env with schedule := choices} accept pool = none)
    (noTimeout : ∀ choices accept, Term.NativeRunner.findTimeout {env with schedule := choices} accept pool = none) :
    ∃ choices, Term.NativeRunner.choose pool env preferred = ({env with schedule := choices}, none) := by
  have readyCore (accept) : Term.Runner.findReady env.toState accept pool = none := ready [] accept
  have noCore (accept) : Term.Runner.findTimeout env.toState accept pool = none := noTimeout [] accept
  have stopped : ∀ choices preferred,
      Term.Runner.choose pool env.toState env.currentPid preferred choices = ([], none) := by
    intro choices
    induction choices with
    | nil =>
      intro preferred
      rw [Term.Runner.choose.eq_def]
      cases preferred <;> simp only [Term.Runner.requested, Term.Runner.runnable,
        readyCore, noCore, Option.map_none, Option.orElse_none]
    | cons choice rest ih =>
      intro preferred
      rw [Term.Runner.choose.eq_def]
      cases preferred <;> simpa only [Term.Runner.requested, Term.Runner.runnable,
        readyCore, noCore, Option.map_none, Option.orElse_none] using ih choice
  exact ⟨[], by simp only [Term.NativeRunner.choose, stopped]⟩

private theorem exclusiveSteps_root {β : Type} {computation : Result Term} {value : Term}
    {before middle after : Nat × List (Nat × String × Term)}
    (peerPoll : Environment → Option (β × Environment)) (peerNext : β → Result Term)
    (trace : ExclusiveSteps [] [1] peerPoll computation before value middle)
    (peerTrace : SharedSteps [1] (.wait peerPoll peerNext) middle childValue after)
    (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice)
    (current : env.currentPid = [] ∨ env.currentPid = [1])
    (counter : env.nativeRefCounter = before.1) (heap : env.nativeHeap = before.2)
    (calm : NativeCalm env.toState := by native_calm) :
    sharedResult (Term.NativeRunner.execute [] env
      (.parallel (.process [] computation some) (.process [1] (.wait peerPoll peerNext) (fun _ => none))) none preferred) =
      (.ok value, after) := by
  induction trace generalizing env preferred with
  | done value shared =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      exact sharedSteps_pendingRoot peerTrace value env preferred current counter heap
  | read read body before final value ready blocked rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have evaluated :=
        ready (Term.NativeRunner.activate env []) rfl counter heap
      have excluded :=
        blocked (Term.NativeRunner.activate env [1]) rfl counter heap
      simp only [Term.NativeRunner.activate] at excluded
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process [] (.nativeGet read) some) (.process [1] (.wait peerPoll peerNext) (fun _ => none))) [] env preferred
        (by intro choices accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, excluded])
        (by intro choices accept; simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
      simp only [Term.NativeRunner.activate] at evaluated
      rw [Term.NativeRunner.execute_eq, selected]
      simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,     evaluated]
      apply ih <;> first | exact peerTrace | exact Or.inl rfl | rfl | exact counter | exact heap | native_calm
  | update read body before middle final value ready blocked rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have evaluated :=
        ready (Term.NativeRunner.activate env []) rfl counter heap
      have excluded :=
        blocked (Term.NativeRunner.activate env [1]) rfl counter heap
      simp only [Term.NativeRunner.activate] at excluded
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process [] (.nativeGet read) some) (.process [1] (.wait peerPoll peerNext) (fun _ => none))) [] env preferred
        (by intro choices accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, excluded])
        (by intro choices accept; simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
      simp only [Term.NativeRunner.activate] at evaluated
      rw [Term.NativeRunner.execute_eq, selected]
      simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,     evaluated]
      rw [Term.NativeRunner.execute_eq]
      simp +contextual [Term.NativeRunner.choose,  Term.Runner.findReady,  Term.NativeRunner.step, Term.Runner.step,  noSignal,
          ]
      apply ih <;> first | exact peerTrace | exact Or.inl rfl | rfl | exact counter | exact heap | native_calm
  | wait poll next reply before middle final value ready blocked rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have polled :=
        ready (Term.NativeRunner.activate env []) rfl counter heap
      simp only [Term.NativeRunner.activate] at polled
      have excluded :=
        blocked (Term.NativeRunner.activate env [1]) rfl counter heap
      simp only [Term.NativeRunner.activate] at excluded
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process [] (.wait poll next) some) (.process [1] (.wait peerPoll peerNext) (fun _ => none))) [] env preferred
        (by intro choices accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, polled, excluded])
        (by intro choices accept; simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
      cases choices <;> rw [Term.NativeRunner.execute_eq, selected]
      all_goals
        simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,     polled, Term.NativeRunner.schedule]
        apply ih <;> first | exact peerTrace | exact Or.inl rfl | rfl | exact counter | exact heap | native_calm

  | modify transition next reply before middle final value ready blocked rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have evaluated :=
        ready (Term.NativeRunner.activate env []) rfl counter heap
      have excluded :=
        blocked (Term.NativeRunner.activate env [1]) rfl counter heap
      simp only [Term.NativeRunner.activate] at excluded
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process [] (.nativeModify transition next) some) (.process [1] (.wait peerPoll peerNext) (fun _ => none))) [] env preferred
        (by intro choices accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, excluded])
        (by intro choices accept; simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
      simp only [Term.NativeRunner.activate] at evaluated
      rw [Term.NativeRunner.execute_eq, selected]
      simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,     evaluated]
      apply ih <;> first | exact peerTrace | exact Or.inl rfl | rfl | exact counter | exact heap | native_calm

private theorem exclusiveSteps_child {β : Type} {computation : Result Term} {value : Term}
    {before middle after : Nat × List (Nat × String × Term)}
    (peerPoll : Environment → Option (β × Environment)) (peerNext : β → Result Term)
    (trace : ExclusiveSteps [1] [] peerPoll computation before value middle)
    (peerTrace : SharedSteps [] (.wait peerPoll peerNext) middle rootValue after)
    (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice)
    (current : env.currentPid = [] ∨ env.currentPid = [1])
    (counter : env.nativeRefCounter = before.1) (heap : env.nativeHeap = before.2)
    (calm : NativeCalm env.toState := by native_calm) :
    sharedResult (Term.NativeRunner.execute [] env
      (.parallel (.process [] (.wait peerPoll peerNext) some) (.process [1] computation (fun _ => none))) none preferred) =
      (.ok rootValue, after) := by
  induction trace generalizing env preferred with
  | done value shared =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      exact sharedSteps_pendingChild peerTrace value env preferred current counter heap
  | read read body before final value ready blocked rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have evaluated :=
        ready (Term.NativeRunner.activate env [1]) rfl counter heap
      have excluded :=
        blocked (Term.NativeRunner.activate env []) rfl counter heap
      simp only [Term.NativeRunner.activate] at excluded
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process [] (.wait peerPoll peerNext) some) (.process [1] (.nativeGet read) (fun _ => none))) [1] env preferred
        (by intro choices accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, excluded])
        (by intro choices accept; simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
      simp only [Term.NativeRunner.activate] at evaluated
      rw [Term.NativeRunner.execute_eq, selected]
      simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,     evaluated]
      apply ih <;> first | exact peerTrace | exact Or.inr rfl | rfl | exact counter | exact heap | native_calm
  | update read body before middle final value ready blocked rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have evaluated :=
        ready (Term.NativeRunner.activate env [1]) rfl counter heap
      have excluded :=
        blocked (Term.NativeRunner.activate env []) rfl counter heap
      simp only [Term.NativeRunner.activate] at excluded
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process [] (.wait peerPoll peerNext) some) (.process [1] (.nativeGet read) (fun _ => none))) [1] env preferred
        (by intro choices accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, excluded])
        (by intro choices accept; simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
      simp only [Term.NativeRunner.activate] at evaluated
      rw [Term.NativeRunner.execute_eq, selected]
      simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,     evaluated]
      rw [Term.NativeRunner.execute_eq]
      simp +contextual [Term.NativeRunner.choose,  Term.Runner.findReady,  Term.NativeRunner.step, Term.Runner.step,  noSignal,
          ]
      apply ih <;> first | exact peerTrace | exact Or.inr rfl | rfl | exact counter | exact heap | native_calm
  | wait poll next reply before middle final value ready blocked rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have polled :=
        ready (Term.NativeRunner.activate env [1]) rfl counter heap
      simp only [Term.NativeRunner.activate] at polled
      have excluded :=
        blocked (Term.NativeRunner.activate env []) rfl counter heap
      simp only [Term.NativeRunner.activate] at excluded
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process [] (.wait peerPoll peerNext) some) (.process [1] (.wait poll next) (fun _ => none))) [1] env preferred
        (by intro choices accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, polled, excluded])
        (by intro choices accept; simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
      cases choices <;> rw [Term.NativeRunner.execute_eq, selected]
      all_goals
        simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,     polled, Term.NativeRunner.schedule]
        apply ih <;> first | exact peerTrace | exact Or.inr rfl | rfl | exact counter | exact heap | native_calm

  | modify transition next reply before middle final value ready blocked rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have evaluated :=
        ready (Term.NativeRunner.activate env [1]) rfl counter heap
      have excluded :=
        blocked (Term.NativeRunner.activate env []) rfl counter heap
      simp only [Term.NativeRunner.activate] at excluded
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process [] (.wait peerPoll peerNext) some) (.process [1] (.nativeModify transition next) (fun _ => none))) [1] env preferred
        (by intro choices accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, excluded])
        (by intro choices accept; simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
      simp only [Term.NativeRunner.activate] at evaluated
      rw [Term.NativeRunner.execute_eq, selected]
      simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,     evaluated]
      apply ih <;> first | exact peerTrace | exact Or.inr rfl | rfl | exact counter | exact heap | native_calm

private theorem exclusiveBlocked_root {β : Type} {computation : Result Term}
    {before after : Nat × List (Nat × String × Term)}
    (peerPoll : Environment → Option (β × Environment)) (peerNext : β → Result Term)
    (trace : ExclusiveBlocked [] [1] peerPoll computation before after)
    (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice)
    (current : env.currentPid = [] ∨ env.currentPid = [1])
    (counter : env.nativeRefCounter = before.1) (heap : env.nativeHeap = before.2)
    (calm : NativeCalm env.toState := by native_calm) :
    sharedResult (Term.NativeRunner.execute [] env
      (.parallel (.process [] computation some) (.process [1] (.wait peerPoll peerNext) (fun _ => none))) none preferred) =
      (.deadlock, after) := by
  induction trace generalizing env preferred with
  | blocked poll next shared stopped excluded =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have stoppedAll :=
        stopped (Term.NativeRunner.activate env []) rfl counter heap
      simp only [Term.NativeRunner.activate] at stoppedAll
      have excludedAll :=
        excluded (Term.NativeRunner.activate env [1]) rfl counter heap
      simp only [Term.NativeRunner.activate] at excludedAll
      obtain ⟨choices, selected⟩ := choose_none_ready
        (.parallel (.process [] (.wait poll next) some)
          (.process [1] (.wait peerPoll peerNext) (fun _ => none))) env preferred
        (by intro choices accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, stoppedAll, excludedAll])
        (by intros; simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
      rw [Term.NativeRunner.execute_eq, selected]
      simp +contextual [  Term.Runner.stop, Term.Runner.isEmpty, Term.Runner.restore, sharedResult, counter, heap]
  | wait poll next reply before middle final ready blocked rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have polled :=
        ready (Term.NativeRunner.activate env []) rfl counter heap
      simp only [Term.NativeRunner.activate] at polled
      have excluded :=
        blocked (Term.NativeRunner.activate env [1]) rfl counter heap
      simp only [Term.NativeRunner.activate] at excluded
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process [] (.wait poll next) some) (.process [1] (.wait peerPoll peerNext) (fun _ => none))) [] env preferred
        (by intro choices accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, polled, excluded])
        (by intro choices accept; simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
      cases choices <;> rw [Term.NativeRunner.execute_eq, selected]
      all_goals
        simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,     polled, Term.NativeRunner.schedule]
        apply ih <;> first | exact Or.inl rfl | rfl | native_calm

private theorem exclusiveBlocked_child {β : Type} {computation : Result Term}
    {before after : Nat × List (Nat × String × Term)}
    (peerPoll : Environment → Option (β × Environment)) (peerNext : β → Result Term)
    (trace : ExclusiveBlocked [1] [] peerPoll computation before after)
    (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice)
    (current : env.currentPid = [] ∨ env.currentPid = [1])
    (counter : env.nativeRefCounter = before.1) (heap : env.nativeHeap = before.2)
    (calm : NativeCalm env.toState := by native_calm) :
    sharedResult (Term.NativeRunner.execute [] env
      (.parallel (.process [] (.wait peerPoll peerNext) some) (.process [1] computation (fun _ => none))) none preferred) =
      (.deadlock, after) := by
  induction trace generalizing env preferred with
  | blocked poll next shared stopped excluded =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have stoppedAll :=
        stopped (Term.NativeRunner.activate env [1]) rfl counter heap
      simp only [Term.NativeRunner.activate] at stoppedAll
      have excludedAll :=
        excluded (Term.NativeRunner.activate env []) rfl counter heap
      simp only [Term.NativeRunner.activate] at excludedAll
      obtain ⟨choices, selected⟩ := choose_none_ready
        (.parallel (.process [] (.wait peerPoll peerNext) some)
          (.process [1] (.wait poll next) (fun _ => none))) env preferred
        (by intro choices accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, stoppedAll, excludedAll])
        (by intros; simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
      rw [Term.NativeRunner.execute_eq, selected]
      simp +contextual [  Term.Runner.stop, Term.Runner.isEmpty, Term.Runner.restore, sharedResult, counter, heap]
  | wait poll next reply before middle final ready blocked rest ih =>
      have noSignal (pid) := (calm pid).1
      have noLinks (pid) := (calm pid).2.1
      have noMonitors (pid) := (calm pid).2.2
      have polled :=
        ready (Term.NativeRunner.activate env [1]) rfl counter heap
      simp only [Term.NativeRunner.activate] at polled
      have excluded :=
        blocked (Term.NativeRunner.activate env []) rfl counter heap
      simp only [Term.NativeRunner.activate] at excluded
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process [] (.wait peerPoll peerNext) some) (.process [1] (.wait poll next) (fun _ => none))) [1] env preferred
        (by intro choices accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, polled, excluded])
        (by intro choices accept; simp +contextual [Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
      cases choices <;> rw [Term.NativeRunner.execute_eq, selected]
      all_goals
        simp +contextual [Term.NativeRunner.step, Term.Runner.step,  noSignal,     polled, Term.NativeRunner.schedule]
        apply ih <;> first | exact Or.inr rfl | rfl | native_calm

/-- Start a two-worker trace through the ordinary spawn implementation. -/
private theorem run_spawn_pair (parent child : Result Term)
    (shared : Nat × List (Nat × String × Term)) (types : List String) (choices : List ScheduleChoice) :
    (Result.schedule {} child (fun _ => parent)).run
      {nativeRefCounter := shared.1, nativeHeap := shared.2, nativeResourceTypes := types} choices =
      let (frame, preferred) := Term.NativeRunner.schedule
        (Term.NativeRunner.save (traceEnv [] [([1], {})] shared types choices))
      Term.NativeRunner.execute [] frame
        (.parallel (.process [] parent some) (.process [1] child (fun _ => none))) none preferred := by
  change Term.Runner.run _ _ _ = _
  rw [Term.Runner.run, Term.Runner.execute]
  simp +contextual [Term.NativeRunner.execute, Term.NativeRunner.schedule, Term.NativeRunner.save,
    traceEnv, Term.Runner.findReady, Term.Runner.step, State.initial, State.process, State.spawnWith,
    State.spawn, State.update]

/-- Two finite, ready critical sections serialize under every finite scheduler
choice list. Each owner excludes the peer's acquisition until release. Both
possible acquisition orders retain their actual poll transitions and may return
different root results. This theorem
assumes ready IO; it makes no claim about external progress or infinite fairness. -/
theorem two_wait_serial_orders
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
  let pool : Term.NativeRunner.Pool Term := .parallel (.process [] (.wait parentPoll parentNext) some)
    (.process [1] (.wait childPoll childNext) (fun _ => none))
  have serial (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice)
      (current : env.currentPid = [] ∨ env.currentPid = [1])
      (counter : env.nativeRefCounter = initial.1) (heap : env.nativeHeap = initial.2)
      (calm : NativeCalm env.toState := by native_calm) :
      sharedResult (Term.NativeRunner.execute [] env pool none preferred) = (.ok rootFirst, parentFinal) ∨
      sharedResult (Term.NativeRunner.execute [] env pool none preferred) = (.ok rootSecond, childFinal) := by
    have noSignal (pid) := (calm pid).1
    have parentPollReady := parentReady (Term.NativeRunner.activate env []) rfl counter heap
    have childPollReady := childReady (Term.NativeRunner.activate env [1]) rfl counter heap
    simp only [Term.NativeRunner.activate] at parentPollReady childPollReady
    have selected := choose_pair_ready pool env preferred current
      (by intro accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [pool, Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, parentPollReady, childPollReady])
      (by intro accept; simp +contextual [pool, Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
    rcases selected with selected | selected
    · left
      rw [Term.NativeRunner.execute_eq, selected]
      cases history : env.schedule
      all_goals
        simp +contextual [pool, Term.NativeRunner.step, Term.Runner.step, noSignal, parentPollReady, Term.NativeRunner.schedule, Term.Runner.schedule,
            history]
        apply exclusiveSteps_root childPoll childNext parent childAfter (calm := ?_) <;>
          first | exact Or.inl rfl | rfl | native_calm
    · right
      rw [Term.NativeRunner.execute_eq, selected]
      cases history : env.schedule
      all_goals
        simp +contextual [pool, Term.NativeRunner.step, Term.Runner.step, noSignal, childPollReady, Term.NativeRunner.schedule, Term.Runner.schedule,
            history]
        apply exclusiveSteps_child parentPoll parentNext child parentAfter (calm := ?_) <;>
          first | exact Or.inr rfl | rfl | native_calm
  change sharedResult (Result.run _ _ choices) = (.ok rootFirst, parentFinal) ∨
    sharedResult (Result.run _ _ choices) = (.ok rootSecond, childFinal)
  simp only [run_spawn_pair]
  cases choices <;> simp only [Term.NativeRunner.schedule, Term.Runner.schedule]
  all_goals apply serial <;> first | exact Or.inl rfl | rfl | native_calm

/-- Two contenders reach one of their blocked owner states for every finite
scheduler choice list. This establishes a crash observation boundary, not IO
progress: neither blocked execution counts as a successful return. -/
theorem two_wait_blocked_orders
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
  let pool : Term.NativeRunner.Pool Term := .parallel (.process [] (.wait parentPoll parentNext) some)
    (.process [1] (.wait childPoll childNext) (fun _ => none))
  have serial (env : Term.NativeRunner.Frame) (preferred : ScheduleChoice)
      (current : env.currentPid = [] ∨ env.currentPid = [1])
      (counter : env.nativeRefCounter = initial.1) (heap : env.nativeHeap = initial.2)
      (calm : NativeCalm env.toState := by native_calm) :
      sharedResult (Term.NativeRunner.execute [] env pool none preferred) = (.deadlock, parentFinal) ∨
      sharedResult (Term.NativeRunner.execute [] env pool none preferred) = (.deadlock, childFinal) := by
    have noSignal (pid) := (calm pid).1
    have parentPollReady := parentReady (Term.NativeRunner.activate env []) rfl counter heap
    have childPollReady := childReady (Term.NativeRunner.activate env [1]) rfl counter heap
    simp only [Term.NativeRunner.activate] at parentPollReady childPollReady
    have selected := choose_pair_ready pool env preferred current
      (by intro accept; cases a : accept [] <;> cases b : accept [1] <;> simp +contextual [pool, Term.NativeRunner.findReady, Term.Runner.findReady, noSignal, a, b, parentPollReady, childPollReady])
      (by intro accept; simp +contextual [pool, Term.NativeRunner.findTimeout, Term.Runner.findTimeout])
    rcases selected with selected | selected
    · left
      rw [Term.NativeRunner.execute_eq, selected]
      cases history : env.schedule
      all_goals
        simp +contextual [pool, Term.NativeRunner.step, Term.Runner.step, noSignal, parentPollReady, Term.NativeRunner.schedule, Term.Runner.schedule,
            history]
        apply exclusiveBlocked_root childPoll childNext parent (calm := ?_) <;>
          first | exact Or.inl rfl | rfl | native_calm
    · right
      rw [Term.NativeRunner.execute_eq, selected]
      cases history : env.schedule
      all_goals
        simp +contextual [pool, Term.NativeRunner.step, Term.Runner.step, noSignal, childPollReady, Term.NativeRunner.schedule, Term.Runner.schedule,
            history]
        apply exclusiveBlocked_child parentPoll parentNext child (calm := ?_) <;>
          first | exact Or.inr rfl | rfl | native_calm
  change sharedResult (Result.run _ _ choices) = (.deadlock, parentFinal) ∨
    sharedResult (Result.run _ _ choices) = (.deadlock, childFinal)
  simp only [run_spawn_pair]
  cases choices <;> simp only [Term.NativeRunner.schedule, Term.Runner.schedule]
  all_goals apply serial <;> first | exact Or.inl rfl | rfl | native_calm

/-- Execute two complete shared-state traces through the actual process pool.
The empty choice list keeps the ready parent current, then runs the child.
Reads and writes stay local steps; IO waits retain their scheduler boundaries. -/
theorem two_shared_serial_steps (parent child : Result Term) (rootValue childValue : Term)
    (before middle after : Nat × List (Nat × String × Term))
    (parentTrace : SharedSteps [] parent before rootValue middle)
    (childTrace : SharedSteps [1] child middle childValue after) :
    (Result.schedule {} child (fun _ => parent)).run {nativeRefCounter := before.1, nativeHeap := before.2} [] =
      (.ok rootValue, {currentPid := [], nativeRefCounter := after.1, nativeHeap := after.2}) := by
  rw [run_spawn_pair]
  simp only [Term.NativeRunner.schedule, Term.Runner.schedule]
  simpa +contextual [traceEnv, Term.NativeRunner.save, Term.NativeRunner.activate,
    State.nativeView, State.view, State.process] using
    (sharedSteps_left parentTrace child none).trans (sharedSteps_right childTrace rootValue [])

/-- Execute complete native calls whose local prefixes register resource types
and decode ownership, then retain all waits of their extracted implementations.
This is the parent-first schedule; it does not establish arbitrary interleavings. -/
theorem two_registered_serial_steps (parent child : Result Term) (rootValue childValue : Term)
    (before middle after : Nat × List (Nat × String × Term))
    (types middleTypes finalTypes : List String)
    (parentTrace : RegisteredSteps [] parent before types rootValue middle middleTypes)
    (childTrace : RegisteredSteps [1] child middle middleTypes childValue after finalTypes) :
    (Result.schedule {} child (fun _ => parent)).run {nativeRefCounter := before.1, nativeHeap := before.2, nativeResourceTypes := types} [] =
      (.ok rootValue, {
        currentPid := [], nativeRefCounter := after.1, nativeHeap := after.2,
        nativeResourceTypes := finalTypes}) := by
  rw [run_spawn_pair]
  simp only [Term.NativeRunner.schedule, Term.Runner.schedule]
  simpa +contextual [traceEnv, Term.NativeRunner.save, Term.NativeRunner.activate,
    State.nativeView, State.view, State.process] using
    (registeredSteps_left parentTrace child none).trans (registeredSteps_right childTrace rootValue [])

section ConcreteNativeTraces

attribute [local simp] traceEnv Term.NativeRunner.findReady Term.NativeRunner.findTimeout Term.NativeRunner.step
  Term.Runner.requested Term.Runner.runnable Term.Runner.findReady Term.Runner.findTimeout
  Term.Runner.step Term.Runner.schedule Term.Runner.isEmpty Term.Runner.restore Term.Runner.stop
  State.nativeView State.view State.process State.storeNative State.store State.update
  State.terminate State.modify State.deliver State.signal State.kill

/-- A complete caller registers and decodes locally, acquires its guard, and
then a peer registers/decodes before attempting the held lock. The blocked peer
cannot run its critical section; the root finishes before the peer acquires.
Every native wait remains a scheduler step. This proves the supplied finite
schedule, not fairness or arbitrary-interleaving safety. -/
theorem two_registered_interleave_steps
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
  rw [run_spawn_pair]
  simp only [Term.NativeRunner.schedule, Term.Runner.schedule]
  change Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [] [([1], {})] s0 types0 [.swap [1]]))
    (.parallel (.process [] parent some) (.process [1] (.nativeGet childRead) (fun _ => none))) none .current = _
  rw [registeredPrefix_left parentPrefix (.nativeGet childRead) none [.swap [1]]]
  rw [Term.NativeRunner.execute_eq]
  simp +contextual [Term.NativeRunner.choose,
    Term.NativeRunner.step,  Term.NativeRunner.save,
     Term.NativeRunner.schedule, traceEnv, acquired]
  have decoder := registeredPrefix_right_switch childPrefix (parentNext parentValue) none
  have blockedStep := sharedSteps_switch_from_blocked parentTrace childPoll childNext types2 none blocked
  have ownerDone := sharedSteps_left parentTrace (.wait childPoll childNext) none types2
  simp +contextual [traceEnv, Term.NativeRunner.save] at decoder blockedStep ownerDone
  rw [decoder, blockedStep, ownerDone]
  rw [Term.NativeRunner.execute_eq]
  simp +contextual [Term.NativeRunner.choose,
    Term.NativeRunner.step,
     Term.NativeRunner.schedule,  childAcquired]
  simpa +contextual [traceEnv, Term.NativeRunner.activate] using
    sharedSteps_right childTrace rootValue [1] types2

/-- Atomic registration/decoding can lead the child prefix in this same concrete
contended schedule. Every IO wait and both ownership suffixes remain in the
certified traces. This does not establish arbitrary schedules or fairness. -/
theorem two_registered_modify_interleave_steps {δ : Type}
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
  rw [run_spawn_pair]
  simp only [Term.NativeRunner.schedule, Term.Runner.schedule]
  change Term.NativeRunner.execute [] (Term.NativeRunner.save (traceEnv [] [([1], {})] s0 types0 [.swap [1]]))
    (.parallel (.process [] parent some) (.process [1] (.nativeModify childTransition childStart) (fun _ => none))) none .current = _
  rw [registeredPrefix_left parentPrefix (.nativeModify childTransition childStart) none [.swap [1]]]
  rw [Term.NativeRunner.execute_eq]
  simp +contextual [Term.NativeRunner.choose,
    Term.NativeRunner.step,  Term.NativeRunner.save,
     Term.NativeRunner.schedule, traceEnv, acquired]
  have decoder := registeredPrefix_modify_right_switch childPrefix (parentNext parentValue) none
  have blockedStep := sharedSteps_switch_from_blocked parentTrace childPoll childNext types2 none blocked
  have ownerDone := sharedSteps_left parentTrace (.wait childPoll childNext) none types2
  simp +contextual [traceEnv, Term.NativeRunner.save] at decoder blockedStep ownerDone
  rw [decoder, blockedStep, ownerDone]
  rw [Term.NativeRunner.execute_eq]
  simp +contextual [Term.NativeRunner.choose,
    Term.NativeRunner.step,
     Term.NativeRunner.schedule,  childAcquired]
  simpa +contextual [traceEnv, Term.NativeRunner.activate] using
    sharedSteps_right childTrace rootValue [1] types2

/-- Two contending workers retain every IO wait in their finite ready traces.
The root acquires first, a child acquisition is attempted while held, then both
traces execute. This is a concrete schedule theorem, not an arbitrary-schedule
or fairness guarantee. -/
theorem two_wait_interleave_steps
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentValue : β) (childValue : γ) (rootValue childResult : Term)
    (s0 s1 s2 s3 s4 : Nat × List (Nat × String × Term)) :
    let atState := fun (pid : PID) (shared : Nat × List (Nat × String × Term)) =>
      ({ currentPid := pid, nativeRefCounter := shared.1, nativeHeap := shared.2 } : Environment)
    parentPoll (atState [] s0) =
      some (parentValue, atState [] s1) →
    SharedSteps [] (parentNext parentValue) s1 rootValue s2 →
    childPoll (atState [1] s1) = none →
    childPoll (atState [1] s2) = some (childValue, atState [1] s3) →
    SharedSteps [1] (childNext childValue) s3 childResult s4 →
    (Result.schedule {} (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext)).run
      { nativeRefCounter := s0.1, nativeHeap := s0.2} [.current, .swap [1]] =
      (.ok rootValue, atState [] s4) := by
  dsimp only
  intro acquired parent blocked childAcquired child
  rw [run_spawn_pair]
  simp only [Term.NativeRunner.schedule, Term.Runner.schedule]
  rw [Term.NativeRunner.execute_eq]
  simp +contextual [Term.NativeRunner.choose,
    Term.NativeRunner.step,  Term.NativeRunner.save,
     Term.NativeRunner.schedule, acquired]
  let env := Term.NativeRunner.save (traceEnv [] [([1], {})] s1)
  let pool : Term.NativeRunner.Pool Term := .parallel
    (.process [] (parentNext parentValue) some) (.process [1] (.wait childPoll childNext) (fun _ => none))
  have selected : Term.NativeRunner.choose pool env (.swap [1]) = Term.NativeRunner.choose pool env .current := by
    dsimp only [pool]
    generalize computationEq : parentNext parentValue = computation at parent ⊢
    cases parent with
    | done => simp +contextual [Term.NativeRunner.choose,  env,
        Term.NativeRunner.save, blocked]
    | read => simp +contextual [Term.NativeRunner.choose,  env,
        Term.NativeRunner.save, blocked]
    | update | modify => simp +contextual [Term.NativeRunner.choose,  env,
        Term.NativeRunner.save, blocked]
    | wait poll next reply before middle final value ready rest =>
      have polled := ready (Term.NativeRunner.activate env []) rfl rfl rfl
      simp +contextual [env, Term.NativeRunner.activate, Term.NativeRunner.save] at polled
      simp +contextual [Term.NativeRunner.choose,  env,
        Term.NativeRunner.save, blocked, polled]
  have fallback : Term.NativeRunner.execute [] env pool none (.swap [1]) =
      Term.NativeRunner.execute [] env pool none .current := by
    conv => lhs; rw [Term.NativeRunner.execute_eq]
    conv => rhs; rw [Term.NativeRunner.execute_eq]
    rw [selected]
  have ownerDone := sharedSteps_left parent (.wait childPoll childNext) none
  simp +contextual [env, pool, traceEnv, Term.NativeRunner.save] at fallback ownerDone
  rw [fallback, ownerDone]
  rw [Term.NativeRunner.execute_eq]
  simp +contextual [Term.NativeRunner.choose,
    Term.NativeRunner.step,
     Term.NativeRunner.schedule,  childAcquired]
  simpa +contextual [traceEnv, Term.NativeRunner.activate] using sharedSteps_right child rootValue [1]

/-- A finite two-worker trace: the root acquires, the child blocks, the root
releases and finishes, then the child acquires and releases. Poll equations
specify every shared-state transition; neither fairness nor unbounded schedule
coverage is assumed. Process-local state is empty throughout this trace. -/
theorem two_wait_interleave
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
  intro acquired parent blocked released parentDone childAcquired child childReleased childDone
  rw [run_spawn_pair]
  simp +contextual [Term.NativeRunner.schedule, Term.Runner.schedule, Term.NativeRunner.execute_eq, Term.NativeRunner.choose,
     Term.NativeRunner.step,  Term.NativeRunner.save,
      Term.NativeRunner.schedule,

    acquired, parent, blocked, released, parentDone, childAcquired, child, childReleased, childDone]

/-- The symmetric finite trace: the child acquires first, the root blocks,
then the child finishes before the root acquires and releases. -/
theorem two_wait_interleave_child_first
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
  intro acquired child blocked released childDone parentAcquired parent parentReleased parentDone
  rw [run_spawn_pair]
  simp +contextual [Term.NativeRunner.schedule, Term.Runner.schedule, Term.NativeRunner.execute_eq, Term.NativeRunner.choose,
     Term.NativeRunner.step,  Term.NativeRunner.save,
      Term.NativeRunner.schedule,

    acquired, child, blocked, released, childDone, parentAcquired, parent, parentReleased, parentDone]


end ConcreteNativeTraces

end Lynx.Result
