module
public meta import Lean
public import Lynx.Concurrent

/-! Kernel-checked certificates for the existing exhaustive terminal-state checker.

Each node certifies every raw successor. Reuse requires equality of the entire
configuration at the same remaining depth. No execution result is trusted. -/

open Lynx Lynx.Concurrent
namespace Lynx.Concurrent.CheckPost

public theorem terminal (α : Type) (accept : Config α → Bool) (depth : Nat) (config : Config α)
    (stopped : config.successors = []) (accepted : accept config = true) :
    checkPost accept (depth + 1) config = true := by
  simpa only [checkPost, stopped] using accepted

public theorem step (α : Type) (accept : Config α → Bool) (depth : Nat) (config : Config α)
    (first : Event × Config α) (rest : List (Event × Config α))
    (successors : config.successors = first :: rest)
    (checked : (first :: rest).all (fun entry => checkPost accept depth entry.2) = true) :
    checkPost accept (depth + 1) config = true := by
  simpa only [checkPost, successors] using checked

public theorem allNil (α : Type) (predicate : Event × Config α → Bool) :
    ([] : List (Event × Config α)).all predicate = true := rfl

public theorem allCons (α : Type) (predicate : Event × Config α → Bool)
    (first : Event × Config α) (rest : List (Event × Config α))
    (head : predicate first = true) (tail : rest.all predicate = true) :
    (first :: rest).all predicate = true := by
  rw [List.all_cons, head, tail]
  rfl

meta section
open Lean Meta Elab Tactic

-- Beta-reduce captured data without repeatedly unfolding recursive functions
-- on unknown arguments under continuations. Constants retain their identity.
private partial def normalize (memo : IO.Ref (Std.HashMap Expr Expr)) (input : Expr) : MetaM Expr := do
  let key ← instantiateMVars input
  if let some value := (← memo.get)[key]? then return value
  let input := key
  let result ← do
    let input := input.consumeMData.headBeta
    let input ← if input.hasLooseBVars || input.isConst || input.isLambda || input.isForall then
        pure input
      else do
        let type ← withTransparency .all (whnf (← inferType input))
        -- A function-valued projection can retain an entire old state (notably
        -- State.elapsed). Reduce projections even when their result is a function.
        let projection ← match input with
          | .proj .. => pure true
          | _ => match input.getAppFn with
            | .const name _ => pure (← getProjectionFnInfo? name).isSome
            | _ => pure false
        if type.isForall && !projection then pure input else withTransparency .all (whnf input)
    match input with
    | .app fn arg =>
        let rebuilt := mkApp (← normalize memo fn) (← normalize memo arg)
        let reduced := rebuilt.headBeta
        if rebuilt == reduced then pure rebuilt else normalize memo reduced
    | .lam name type body info =>
        pure (.lam name type (← normalize memo body) info)
    | .letE _ _ value body _ => normalize memo (body.instantiate1 value)
    | .proj type idx value =>
        let value ← normalize memo value
        let result := .proj type idx value
        if result.hasLooseBVars then pure result else do
          let reduced ← withTransparency .all (whnf result)
          if reduced == result then pure result else normalize memo reduced
    | .mdata _ value => normalize memo value
    | _ => pure input
  let result ← instantiateMVars result
  if !key.hasMVar && !result.hasMVar then memo.modify (·.insert key result)
  return result

private partial def processKeys (memo : IO.Ref (Std.HashMap Expr Expr)) (expr : Expr) (keys : Array Expr := #[]) : MetaM (Array Expr) := do
  let expr := expr.consumeMData
  if !expr.hasLooseBVars || expr.isLambda || expr.isForall then return keys
  if let .app fn arg := expr then
    if !fn.hasLooseBVars then
      let type ← withTransparency .all (whnf (← inferType fn))
      if type.isForall && !type.bindingBody!.hasLooseBVars then
        let optionType := mkApp (mkConst ``Option [0]) (mkConst ``ProcessState)
        if (← isDefEq type.bindingDomain! (mkConst ``PID)) && (← isDefEq type.bindingBody! optionType) then
          let fn' ← withTransparency .all (whnf fn)
          if fn'.isLambda then return ← processKeys memo (mkApp fn' arg).headBeta keys
  let mut keys := keys
  if expr.isAppOfArity ``Eq 3 then
    let one := expr.getArg! 1
    let two := expr.getArg! 2
    let key := if one == .bvar 0 then some two else if two == .bvar 0 then some one else none
    if let some key := key then
      if !key.hasLooseBVars && (← isDefEq (expr.getArg! 0) (mkConst ``PID)) then
        let key ← normalize memo key
        unless keys.contains key do keys := keys.push key
  match expr with
  | .app fn arg => processKeys memo arg (← processKeys memo fn keys)
  | .proj _ _ value => processKeys memo value keys
  | _ => return keys

private def canonicalize (memo : IO.Ref (Std.HashMap Expr Expr)) (config : Expr) : TacticM (Expr × Expr) := do
  unless config.isAppOfArity ``Config.running 5 do return (config, ← mkEqRefl config)
  let state ← withTransparency .all (whnf (config.getArg! 1))
  unless state.isAppOfArity ``Lynx.Concurrent.State.mk 8 do throwError "postcondition search expected a runtime state"
  let processes := state.getArg! 0
  let function ← withTransparency .all (whnf processes)
  unless function.isLambda do throwError "postcondition search expected a process map"
  let keys ← processKeys memo function.bindingBody!
  let keys := keys.qsort (fun first second => first.hash < second.hash)
  let pidType := mkConst ``PID
  let canonical ← withLocalDeclD `candidate pidType fun candidate => do
    let mut result := mkApp (mkConst ``Option.none [0]) (mkConst ``ProcessState)
    for key in keys.toList.reverse do
      let value ← normalize memo (mkApp processes key)
      result ← mkAppM ``ite #[← mkEq candidate key, value, result]
    mkLambdaFVars #[candidate] result
  let functionProof ← if ← isDefEq processes canonical then mkEqRefl canonical else do
    let equality ← mkEq processes canonical
    let goal ← mkFreshExprSyntheticOpaqueMVar equality
    let candidate := mkIdent `candidate
    let (initial, _) ← Elab.runTactic goal.mvarId! (← `(tactic| funext $candidate)) (ctx := {errToSorry := false})
    let mut goals := initial
    for key in keys do
      let key ← PrettyPrinter.delab key
      let mut pending := []
      for current in goals do
        let (split, _) ← Elab.runTactic current (← `(tactic| by_cases $candidate = $key)) (ctx := {errToSorry := false})
        pending := pending ++ split
      goals := pending
    let mut unsolved := []
    for current in goals do
      let (pending, _) ← Elab.runTactic current (← `(tactic|
        first
          | rfl
          | simp_all [Lynx.Concurrent.State.update, Lynx.Concurrent.State.modify,
              Lynx.Concurrent.State.process, Lynx.Concurrent.State.initial, Lynx.Concurrent.State.store,
              Lynx.Concurrent.State.storeNative, Lynx.Concurrent.State.nativeView, Lynx.Concurrent.State.view,
              Lynx.Concurrent.State.terminate, Lynx.Concurrent.State.append, Lynx.Concurrent.State.receive,
              Lynx.Concurrent.State.spawnWith, Lynx.Concurrent.State.spawn, Lynx.Concurrent.State.emit, enqueue]))
        (ctx := {errToSorry := false})
      unsolved := unsolved ++ pending
    unless unsolved.isEmpty do
      IO.eprintln s!"map keys {keys}"
      for pending in unsolved do IO.eprintln s!"map goal {← ppExpr (← pending.getType)}"
      throwError "postcondition search could not certify its process-map normalization"
    let proof ← instantiateMVars goal
    unless !proof.hasMVar && !proof.hasSorry do throwError "incomplete process-map certificate"
    pure proof
  let stateArgs := state.getAppArgs
  let stateProof ← withLocalDeclD `processes (← inferType processes) fun functions => do
    mkCongrArg (← mkLambdaFVars #[functions] (mkAppN state.getAppFn (stateArgs.set! 0 functions))) functionProof
  let cfgArgs := config.getAppArgs
  let cfgProof ← withLocalDeclD `state (mkConst ``Lynx.Concurrent.State) fun value => do
    mkCongrArg (← mkLambdaFVars #[value] (mkAppN config.getAppFn (cfgArgs.set! 1 value))) stateProof
  let result := mkAppN config.getAppFn (cfgArgs.set! 1 (mkAppN state.getAppFn (stateArgs.set! 0 canonical)))
  return (result, cfgProof)

private partial def listItems (input : Expr) : MetaM (Array Expr) := do
  let input ← withTransparency .all (whnf input)
  if input.isAppOfArity ``List.nil 1 then return #[]
  unless input.isAppOfArity ``List.cons 3 do
    throwError "postcondition search could not enumerate successors: {input}"
  return #[input.getArg! 1] ++ (← listItems (input.getArg! 2))

private def pair (input : Expr) : MetaM (Expr × Expr) := do
  let input ← withTransparency .all (whnf input)
  unless input.isAppOfArity ``Prod.mk 4 do throwError "postcondition search expected an event/configuration pair"
  return (input.getArg! 2, input.getArg! 3)

private def declaration (locals : Array Expr) (type value : Expr) (isTheorem : Bool) : TacticM Expr := do
  let type ← mkForallFVars locals type
  let value ← mkLambdaFVars locals value
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  unless !value.hasMVar && !value.hasFVar && !value.hasSorry do
    throwError "postcondition certificate has an incomplete dependency"
  let name ← mkAuxDeclName (if isTheorem then `postCertificate else `postConfiguration)
  let levels := (collectLevelParams {} type).params.toList
  if isTheorem then
    addDecl (.thmDecl {name := name, levelParams := levels, type := type, value := value})
  else
    addDecl (.defnDecl {name := name, levelParams := levels, type := type, value := value, hints := .regular 0, safety := .safe})
  enableRealizationsForConst name
  let context ← getLCtx
  let args := locals.filter fun expr => !(context.get! expr.fvarId!).isLet
  return mkAppN (mkConst name (levels.map mkLevelParam)) args

private structure Entry where
  value : Expr
  depth : Nat
  config : Expr
  proof : Expr

private structure Search where
  cache : Std.HashMap Expr Entry := {}
  hits : Nat := 0
  nodes : Nat := 0

private def transport (accept : Expr) (depth : Nat) (equal checked : Expr) : MetaM Expr := do
  let cfgType := (← inferType equal).getArg! 0
  withLocalDeclD `next cfgType fun next => do
    let test ← mkAppM ``checkPost #[accept, mkNatLit depth, next]
    let pred ← mkEq test (mkConst ``Bool.true)
    let fn ← mkLambdaFVars #[next] pred
    let typeEq ← mkCongrArg fn equal
    mkAppM ``Eq.mpr #[typeEq, checked]

private partial def prove (locals : Array Expr) (accept : Expr) (depth : Nat) (raw : Expr)
    (state : IO.Ref Search) (limit : Nat) (memo : IO.Ref (Std.HashMap Expr Expr)) : TacticM (Expr × Expr × Expr) := do
  if depth == 0 then throwError "postcondition search exhausted its step bound"
  let normalized ← normalize memo raw
  let (config, normalizedEq) ← canonicalize memo normalized
  let config ← instantiateMVars config
  let key ← instantiateMVars (← mkAppM ``checkPost #[accept, mkNatLit depth, config])
  let mut cached? := (← state.get).cache[key]?
  if cached?.isNone then
    for (_, candidate) in (← state.get).cache do
      if candidate.depth == depth && (← withTransparency .all (isDefEq config candidate.value)) then
        cached? := some candidate
        break
  if let some cached := cached? then
    state.modify fun s => {s with hits := s.hits + 1}
    let equal ← declaration locals (← mkEq raw cached.config) normalizedEq true
    return (cached.config, cached.proof, equal)
  unless (← state.get).nodes < limit do throwError "postcondition search exhausted its node bound"
  state.modify fun s => {s with nodes := s.nodes + 1}
  let cfgType ← inferType raw
  let alias ← declaration locals cfgType config false
  let α := cfgType.getArg! 0
  let pairType ← mkAppM ``Prod #[mkConst ``Event, cfgType]
  let successors ← mkAppM ``Config.successors #[alias]
  let evaluated ← Lean.Meta.Tactic.Cbv.cbvEntry successors
  let (successorValue, successorProof) ← match evaluated with
    | .rfl .. => pure (successors, ← mkEqRefl successors)
    | .step value proof .. => pure (value, proof)
  let entries ← listItems successorValue
  let mut rawPairs : Array Expr := #[]
  let mut canonicalPairs : Array Expr := #[]
  let mut equalities : Array Expr := #[]
  let mut certificates : Array Expr := #[]
  for entry in entries do
    let (event, next) ← pair entry
    let (named, checked, equal) ← prove locals accept (depth - 1) next state limit memo
    let rawPair ← mkAppM ``Prod.mk #[event, next]
    let namedPair ← mkAppM ``Prod.mk #[event, named]
    let pairEq ← withLocalDeclD `next cfgType fun next' => do
      let fn ← mkLambdaFVars #[next'] (← mkAppM ``Prod.mk #[event, next'])
      mkCongrArg fn equal
    rawPairs := rawPairs.push rawPair
    canonicalPairs := canonicalPairs.push namedPair
    equalities := equalities.push pairEq
    certificates := certificates.push checked
  let rawList ← mkListLit pairType rawPairs.toList
  let mut listEq ← mkEqRefl (← mkListLit pairType [])
  let mut rawTail ← mkListLit pairType []
  let mut namedTail ← mkListLit pairType []
  let predicate ← withLocalDeclD `entry pairType fun entry => do
    mkLambdaFVars #[entry] (← mkAppM ``checkPost #[accept, mkNatLit (depth - 1), ← mkAppM ``Prod.snd #[entry]])
  let mut allChecked := mkAppN (mkConst ``allNil) #[α, predicate]
  for idx in (List.range entries.size).reverse do
    let firstEq ← withLocalDeclD `head pairType fun head => do
      mkCongrArg (← mkLambdaFVars #[head] (← mkAppM ``List.cons #[head, rawTail])) equalities[idx]!
    let secondEq ← mkCongrArg (← mkAppM ``List.cons #[canonicalPairs[idx]!]) listEq
    listEq ← mkEqTrans firstEq secondEq
    allChecked := mkAppN (mkConst ``allCons) #[α, predicate, canonicalPairs[idx]!, namedTail, certificates[idx]!, allChecked]
    rawTail ← mkAppM ``List.cons #[rawPairs[idx]!, rawTail]
    namedTail ← mkAppM ``List.cons #[canonicalPairs[idx]!, namedTail]
  let evaluatedEq ← mkEqTrans successorProof (← mkEqRefl rawList)
  let definitional ← declaration locals (← mkEq successors rawList) evaluatedEq true
  let successorsEq ← mkEqTrans definitional listEq
  let proof ← if entries.isEmpty then do
      unless ← isDefEq (mkApp accept alias) (mkConst ``Bool.true) do
        throwError "postcondition rejected at a terminal configuration"
      let accepted ← declaration locals (← mkEq (mkApp accept alias) (mkConst ``Bool.true))
        (← mkEqRefl (mkConst ``Bool.true)) true
      pure (mkAppN (mkConst ``terminal) #[α, accept, mkNatLit (depth - 1), alias, successorsEq, accepted])
    else
      pure (mkAppN (mkConst ``step) #[α, accept, mkNatLit (depth - 1), alias,
        canonicalPairs[0]!, ← mkListLit pairType canonicalPairs.toList.tail!, successorsEq, allChecked])
  let target ← mkEq (← mkAppM ``checkPost #[accept, mkNatLit depth, alias]) (mkConst ``Bool.true)
  let checked ← declaration locals target proof true
  state.modify fun s => {s with cache := s.cache.insert key ⟨config, depth, alias, checked⟩}
  let equal ← declaration locals (← mkEq raw alias) normalizedEq true
  return (alias, checked, equal)

/-- Certify `checkPost accept depth config = true` by sharing proofs of repeated
configurations. The finite depth and node budgets fail closed. Every generated
normalization and successor certificate is checked by Lean's kernel. -/
syntax (name := checkPostTactic) "lynx_check_post" : tactic

@[tactic checkPostTactic] public meta def evalCheckPost : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let type ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := type.eq? | throwError "expected a checkPost equality"
  unless lhs.isAppOfArity ``checkPost 4 && rhs.isConstOf ``Bool.true do
    throwError "expected checkPost accept depth config = true"
  let depth ← getNatValue? (lhs.getArg! 2)
  let some depth := depth | throwError "postcondition search needs a concrete step bound"
  let locals ← (← getLCtx).foldlM (init := #[]) fun xs decl =>
    pure (if decl.isImplementationDetail then xs else xs.push decl.toExpr)
  let state ← IO.mkRef ({} : Search)
  let memo ← IO.mkRef ({} : Std.HashMap Expr Expr)
  let (_, checked, equal) ← prove locals (lhs.getArg! 1) depth (lhs.getArg! 3) state 20000 memo
  let result ← transport (lhs.getArg! 1) depth equal checked
  goal.assign result
  replaceMainGoal []
end
end Lynx.Concurrent.CheckPost
