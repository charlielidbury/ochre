import Ochr.Meaning.Steps.Machine.Attr
import Ochr.Meaning.Steps.Machine.Comb

/-!
# `grows_go`: the closure, by the head of the computation

`grows_go` (or `grows_go ih`) proves `GrowsIn G x` by walking `x`: at each goal it reads the head
constant of the computation and applies the `@[grows]` lemmas registered for it (in order, the
first that applies), or, for a function that is a field of the induction hypothesis `ih` (a
structure whose fields are named after the machine's functions), that field. A `match` is split,
a `let` and a β-redex are reduced, a binder is introduced, an `OnTab` side condition is an
assumption, and a write that keeps the tables is closed by `rfl`s. A goal no rule applies to is
left open (`grows_go` never fails), so the caller sees exactly what is missing.

Every rule is chosen by the head constant, never by unfolding, so a large remainder of a `do`
block is never reduced (the slice's note: matching by reducible unfolding only, or `whnf` times
out).
-/

namespace Ochr.Meaning.Steps.Machine

open Lean Meta Elab Tactic

attribute [grows] growsIn_bind
attribute [grows] growsIn_get_bind
attribute [grows] growsIn_enterWorld_bind
attribute [grows] growsIn_get_restore
attribute [grows] growsIn_pure growsIn_err growsIn_exhausted growsIn_throw growsIn_stuckNow growsIn_stuckOn
attribute [grows] growsIn_ite growsIn_dite growsIn_map growsIn_discard growsIn_get
attribute [grows] growsIn_forIn_range growsIn_forIn_array growsIn_forIn_list
attribute [grows] growsIn_forIn_list_mem
attribute [grows] growsIn_mapM_list growsIn_mapM_array growsIn_anyM_list growsIn_allM_list growsIn_foldlM_list
attribute [grows] growsIn_mapM_list_mem growsIn_mapM_option
attribute [grows] growsIn_tryCatch growsIn_tryCatchThe growsIn_onFail growsIn_catchStuck growsIn_locateErrors
attribute [grows] growsIn_tick growsIn_modifyThe_log growsIn_getThe_fuel
attribute [grows] growsIn_withLive growsIn_withErased growsIn_withErasedIf growsIn_withRuntime growsIn_withCopying
attribute [grows] growsIn_restoreKeep growsIn_restoreNames growsIn_exitWorld growsIn_inWorld growsIn_privately growsIn_inStatement
attribute [grows] growsIn_freshAbs growsIn_freshLoan growsIn_underCheck
attribute [grows] growsIn_modify

/-- The rfl-proof of a write that keeps the tables. -/
theorem tablesGrow_of_eq {s s' : MState} (h₁ : s'.globals = s.globals) (h₂ : s'.inds = s.inds)
    (h₃ : s'.absDecl = s.absDecl) (h₄ : s'.nextAbs = s.nextAbs) (h₅ : s'.nextLoan = s.nextLoan) :
    TablesGrow s s' :=
  ⟨h₁, h₂, h₃ ▸ Nat.le_refl _, fun _ _ => by rw [h₃], h₄ ▸ Nat.le_refl _, h₅ ▸ Nat.le_refl _⟩

/-- Open a hypothesis's binders and `have`s into metavariables, at reducible transparency. -/
partial def openHyp (ty : Expr) : MetaM (Array Expr × Expr) := do
  let (mvs, _, c) ← withReducible <| forallMetaTelescopeReducing ty
  match c.consumeMData with
  | .letE _ _ v b _ =>
    let (mvs', c') ← openHyp (b.instantiate1 v)
    pure (mvs ++ mvs', c')
  | c => pure (mvs, c)

/-- The `GrowsIn` conclusions a proof `e : T` gives: `T`'s binders and `have`s opened into
metavariables, and a conjunction split into its two sides. -/
partial def growsConcls (e : Expr) : MetaM (List (Expr × Array Expr × Expr)) := do
  let (mvs, c) ← openHyp (← instantiateMVars (← inferType e))
  let pf := mkAppN e mvs
  if c.isAppOfArity ``And 2 then
    let l ← growsConcls (← mkAppM ``And.left #[pf])
    let r ← growsConcls (← mkAppM ``And.right #[pf])
    return (l ++ r).map fun (p, ms, c) => (p, mvs ++ ms, c)
  if c.getAppFn.constName? == some ``GrowsIn then return [(pf, mvs, c)]
  return []

/-- Apply the first local hypothesis (or one side of a conjunction) whose conclusion is a
`GrowsIn` and that applies (its binders, `have`s included, opened at reducible transparency). -/
def applyGrowsHyp (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let target ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let st ← saveState
    let cs ← (growsConcls d.toExpr) <|> pure []
    for (pf, mvs, concl) in cs do
      let s ← saveState
      if ← withReducible (isDefEq concl target) then
        g.assign (← instantiateMVars pf)
        let gs ← mvs.toList.filterMapM fun m => do
          let m := m.mvarId!
          if ← m.isAssigned then pure none else pure (some m)
        return gs
      s.restore
    st.restore
  throwError "apply_grows_hyp: no hypothesis applies"

elab "apply_grows_hyp" : tactic => do
  let g ← getMainGoal
  replaceMainGoal (← applyGrowsHyp g)

/-- Close a goal by a hypothesis `∀ …, a = C … → False` whose equation holds by `rfl` (the
excluded cases of a functional induction's catch-all). -/
def growsAbsurd (g : MVarId) : MetaM Unit := g.withContext do
  let target ← instantiateMVars (← g.getType)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let s ← saveState
    let ok ← (do
      let (mvs, _, concl) ← withReducible <| forallMetaTelescopeReducing (← instantiateMVars d.type)
      unless concl.isFalse && mvs.size > 0 do return false
      let last := mvs.back!
      let some (_, a, b) := (← instantiateMVars (← inferType last)).eq? | return false
      unless ← isDefEq a b do return false
      last.mvarId!.assign (← mkEqRefl a)
      let pf ← instantiateMVars (mkAppN d.toExpr mvs)
      if pf.hasExprMVar then return false
      g.assign (← mkFalseElim target pf)
      pure true) <|> pure false
    if ok then return
    s.restore
  throwError "grows_absurd: no hypothesis refutes the case"

/-- After a split on the fuel: `n + 1 = k + 1` substitutes `k := n`, `0 = k + 1` closes the
goal. Returns the goal left, if any. -/
partial def fuelCleanup (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (α, _, _) := ty.eq? | continue
    unless α.isConstOf ``Nat do continue
    -- a constructor mismatch closes the goal
    if let some r ← (do
        if ← g.contradictionCore {} then pure (some none) else pure none) <|> pure none then
      return r
    let r? ← (do
      let pf ← mkAppM ``Nat.succ.inj #[d.toExpr]
      let pfTy ← inferType pf
      let g1 ← g.assert `hfuel pfTy pf
      let (fv, g2) ← g1.intro1P
      let g3 ← g2.clear d.fvarId
      let g4 ← subst g3 fv
      pure (some g4)) <|> pure none
    if let some g' := r? then return ← fuelCleanup g'
  return some g

/-- One step of the closure on the main goal. Throws if no rule applies. -/
def growsStep (ih? : Option Name) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
  let t ← instantiateMVars (← g.getType)
  let t := t.consumeMData.headBeta
  if t.isForall then
    -- `∀ a ∈ l, P a` over a list written out or mapped: one goal per element
    if let .forallE _ _ (.forallE _ (hyp : Expr) _ _) _ := t then
      let hyp := hyp.consumeMData
      if hyp.isAppOfArity ``Membership.mem 5 then
        let l := (hyp.getArg! 3).consumeMData
        let tac ← match l.getAppFn.constName? with
          | some ``List.cons => some <$> `(tactic| rw [List.forall_mem_cons])
          | some ``List.nil => some <$> `(tactic| exact List.forall_mem_nil _)
          | some ``List.map => some <$> `(tactic| rw [List.forall_mem_map])
          | _ => pure none
        if let some tac := tac then
          evalTactic tac
          return
    evalTactic (← `(tactic| intro))
    return
  if t.isLet then
    evalTactic (← `(tactic| intro))
    return
  match t.getAppFn.constName? with
  | some ``OnTab => evalTactic (← `(tactic| assumption))
  | some ``And => evalTactic (← `(tactic| constructor))
  | some ``Membership.mem => evalTactic (← `(tactic| assumption))
  | some ``Steps.TablesGrow =>
    evalTactic (← `(tactic| exact tablesGrow_of_eq rfl rfl rfl rfl rfl))
  | some ``GrowsIn =>
    let x := t.appArg!.consumeMData
    if x.isLet || x.isHeadBetaTarget || x.isMData then
      evalTactic (← `(tactic| dsimp only))
      return
    if x.getAppFn.isFVar then
      -- a computation given as a hypothesis (a continuation, a run passed in)
      evalTactic (← `(tactic| first | assumption | (apply_grows_hyp)))
      return
    let some f := x.getAppFn.constName? | throwError "grows_step: no constant head in {x}"
    if (← getMatcherInfo? f).isSome then
      -- a match on a constructor (the fuel's `n + 1`) reduces; any other is split
      match ← reduceMatcher? x with
      | .reduced x' =>
        let g' ← g.replaceTargetDefEq (mkApp t.appFn! x')
        replaceMainGoal [g']
      | _ =>
        evalTactic (← `(tactic| split))
        let gs ← getGoals
        setGoals (← gs.filterMapM fun g => fuelCleanup g)
      return
    -- a bind whose computation returns a computation: the induction hypothesis's `fRet` field
    -- says what the returned computation does (`growsIn_bind_ret`)
    if f == ``Bind.bind then
      if let some ih := ih? then
        let args := x.getAppArgs
        if args.size == 6 then
          if let some f0 := args[4]!.getAppFn.constName? then
            let ihDecl ← getLocalDeclFromUserName ih
            let ihTy ← whnfR (← instantiateMVars ihDecl.type)
            if let some S := ihTy.getAppFn.constName? then
              let fld := Name.mkSimple (f0.componentsRev.head!.toString ++ "Ret")
              if isStructure (← getEnv) S && (getStructureFields (← getEnv) S).contains fld then
                let proj := mkIdent (ih ++ fld)
                let gs ← g.apply (← mkConstWithFreshMVarLevels `Ochr.Meaning.Steps.Machine.growsIn_bind_ret)
                let mut out := #[]
                for g' in gs do
                  let ty ← instantiateMVars (← g'.getType)
                  if ty.getAppFn.constName? == some `Ochr.Meaning.Steps.Machine.RetOk then
                    setGoals [g']
                    evalTactic (← `(tactic| apply $proj))
                    out := out ++ (← getGoals)
                  else out := out.push g'
                setGoals (← out.toList.filterM fun g' => do pure !(← g'.isAssigned))
                return
    -- the induction hypothesis's field named after `f`
    if let some ih := ih? then
      let ihDecl ← getLocalDeclFromUserName ih
      let ihTy ← whnfR (← instantiateMVars ihDecl.type)
      if let some S := ihTy.getAppFn.constName? then
        if isStructure (← getEnv) S then
          let fld := f.componentsRev.head!
          if (getStructureFields (← getEnv) S).contains fld then
            let proj := mkIdent (ih ++ fld)
            evalTactic (← `(tactic| apply $proj))
            return
    for lem in growsLemmas (← getEnv) f do
      let ok ← (do
        let gs ← withReducible <| g.apply (← mkConstWithFreshMVarLevels lem)
        replaceMainGoal gs; pure true) <|> pure false
      if ok then return
    -- a local hypothesis (an induction hypothesis stated as a `∀`)
    let ok ← (do replaceMainGoal (← applyGrowsHyp g); pure true) <|> pure false
    if ok then return
    -- a projection of a computation still under a `match` (an arm of a list of pairs)
    if (← getProjectionFnInfo? f).isSome then
      let ok ← (do evalTactic (← `(tactic| first | dsimp only | split)); pure true) <|> pure false
      if ok then return
    -- an excluded case
    let ok ← (do growsAbsurd g; replaceMainGoal []; pure true) <|> pure false
    if ok then return
    throwError "grows_step: no rule for {f}"
  | _ => throwError "grows_step: not a closure goal"

/-- The closure to the end: every goal is walked until no rule applies. -/
partial def growsGo (ih? : Option Name) : TacticM Unit := do
  let gs ← getGoals
  let mut out : Array MVarId := #[]
  for g in gs do
    if ← g.isAssigned then continue
    setGoals [g]
    let ok ← (do growsStep ih?; pure true) <|> pure false
    if ok then
      growsGo ih?
      out := out ++ (← getGoals)
    else
      out := out.push g
  setGoals out.toList

/-- After a split on the fuel: substitute `n + 1 = k + 1`, close `0 = k + 1`. -/
elab "fuel_cleanup" : tactic => do
  let g ← getMainGoal
  match ← fuelCleanup g with
  | some g' => replaceMainGoal [g']
  | none => replaceMainGoal []

elab "grows_go" : tactic => growsGo none
elab "grows_go" ppSpace colGt ih:ident : tactic => growsGo (some ih.getId)

/-- The heads of the computations of the open goals (to see what is missing). -/
elab "grows_heads" : tactic => do
  for g in ← getGoals do
    let t := (← instantiateMVars (← g.getType)).consumeMData
    if t.getAppFn.constName? == some ``GrowsIn then
      let x := t.appArg!
      logInfo m!"open: {x.getAppFn}"
    else logInfo m!"open: {t}"

end Ochr.Meaning.Steps.Machine
