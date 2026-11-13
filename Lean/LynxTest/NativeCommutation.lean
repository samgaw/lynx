module

import Lynx
meta import LynxTest.ProofAudit

namespace LynxTest.NativeCommutation
open Lynx Concurrent

private def joined : Result :=
  Result.schedule {} (.nativeGet fun _ =>
    .nativeModify (fun env => ((), {env with nativeRefCounter := env.nativeRefCounter + 1}))
      fun _ => .send [] .true (.ok .nil)) fun _ =>
    .nativeModify (fun env => ((), {env with nativeRefCounter := env.nativeRefCounter + 1})) fun _ =>
      .receive .infinity (fun _ message => some message) fun _ =>
        .wait (fun env => some ((), env)) fun _ => .ok .true

private def competing : Result :=
  Result.schedule {} (.nativeModify (fun env => ((), {env with nativeRefCounter := 1}))
    fun _ => .ok .nil) fun _ =>
    .nativeModify (fun env => ((), {env with nativeRefCounter := 2})) fun _ => .ok .true

private def joinedStart : Config Term := .start {} joined (fun _ _ => 0)
private def competingStart : Config Term := .start {} competing (fun _ _ => 0)

meta section
open Lean Meta Elab Command

private partial def listItems (expr : Expr) : MetaM (Array Expr) := do
  let expr ← whnf expr
  if expr.isAppOfArity ``List.nil 1 then return #[]
  unless expr.isAppOfArity ``List.cons 3 do throwError "audit expected a closed list: {expr}"
  return #[expr.getArg! 1] ++ (← listItems (expr.getArg! 2))

private def pair (expr : Expr) : MetaM (Expr × Expr) := do
  let expr ← whnf expr
  unless expr.isAppOfArity ``Prod.mk 4 do throwError "audit expected a pair: {expr}"
  return (expr.getArg! 2, expr.getArg! 3)

-- Normalize data fields while retaining conditionals under function binders;
-- those are discharged extensionally by the kernel-checked square proof.
private def normalizeData (expr : Expr) : MetaM Expr :=
  transform expr (pre := fun expr => do
    let expr ← whnf expr
    return if expr.isLambda then .done expr else .continue expr)

private def steps (config : Expr) : MetaM (Array (Expr × Expr × Expr)) := do
  let entries ← listItems (← mkAppM ``Config.steps #[config])
  entries.mapM fun entry => do
    let (key, rest) ← pair entry
    let (event, next) ← pair rest
    return (key, event, ← normalizeData next)

/-- Enumerate actual successors, not reduced paths. For each reported commuting
pair, find the reversed path with the same events and exact final configuration.
Every successful square is additionally submitted to the kernel as an equality. -/
private def audit (start : Expr) (budget : Nat) (incorrect : Bool := false) : MetaM (Nat × Nat) :=
  withTransparency .all do
    let mut pending := #[(start, budget)]
    let mut visited : Array Expr := #[]
    let mut squares := 0
    while !pending.isEmpty do
      let (config, fuel) := pending.back!
      pending := pending.pop
      if ← visited.anyM (isDefEq config) then continue
      visited := visited.push config
      let firsts ← steps config
      for (firstKey, firstEvent, afterFirst) in firsts do
        for (secondKey, secondEvent, last) in ← steps afterFirst do
          let commuting ← whnf (← mkAppM ``Config.commutesWith #[config, firstKey, secondKey])
          unless incorrect || commuting.isConstOf ``Bool.true do continue
          -- Even the deliberately broken classifier excludes identical actors.
          if ← isDefEq firstKey secondKey then continue
          let mut reversed := false
          for (key, event, afterSecond) in firsts do
            unless (← isDefEq key secondKey) && (← isDefEq event secondEvent) do continue
            for (key', event', last') in ← steps afterSecond do
              unless (← isDefEq key' firstKey) && (← isDefEq event' firstEvent) do continue
              let equality ← mkEq (← normalizeData last) (← normalizeData last')
              let hole ← mkFreshExprSyntheticOpaqueMVar equality
              let proved ← try
                let (goals, _) ← Elab.runTactic hole.mvarId! (← `(tactic|
                  congr 2 <;> first
                    | rfl
                    | (solve | simp [Task.ended, State.terminate, Task.delivery, State.receive, State.append,
                        State.update, State.modify, State.process, State.initial, State.nativeView,
                        State.view, State.storeNative, State.store, State.emit, enqueue])
                    | (funext pid
                       by_cases root : pid = ([] : PID) <;>
                         by_cases child : pid = ([1] : PID) <;>
                         simp_all [Task.ended, State.terminate, Task.delivery, State.receive, State.append,
                           State.update, State.modify, State.process, State.initial, State.nativeView,
                           State.view, State.storeNative, State.store, State.emit, enqueue])))
                  (ctx := {errToSorry := false})
                pure goals.isEmpty
              catch _ => pure false
              unless proved do continue
              let proof ← instantiateMVars hole
              unless !proof.hasMVar && !proof.hasSorry do throwError "audit produced an incomplete proof"
              let name ← mkFreshUserName `nativeCommutingSquare
              addDecl (.thmDecl {name := name, levelParams := [], type := equality, value := proof})
              squares := squares + 1
              reversed := true
              break
            if reversed then break
          unless reversed do throwError "native commutation audit found a noncommuting pair"
      let successors ← listItems (← mkAppM ``Config.successors #[config])
      unless successors.isEmpty || fuel > 0 do throwError "native audit exhausted its exploration budget"
      for successor in successors do
        let (_, next) ← pair successor
        pending := pending.push (← normalizeData next, fuel - 1)
    return (visited.size, squares)

end

open Lean Elab Command

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
run_cmd do
  let (states, squares) ← liftTermElabM do audit (mkConst ``joinedStart) 24
  unless states > 0 && squares > 0 do throwError "native commutation audit exercised no commuting pairs"
  logInfo m!"native commutation audit: {states} configurations, {squares} kernel-checked squares"
  let rejected ← liftTermElabM do
    try
      let _ ← audit (mkConst ``competingStart) 16 true
      return false
    catch error =>
      let message ← error.toMessageData.toString
      unless message == "native commutation audit found a noncommuting pair" do throw error
      return true
  unless rejected do throwError "native commutation audit accepted a deliberately incorrect classifier"

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.NativeCommutation

end LynxTest.NativeCommutation
