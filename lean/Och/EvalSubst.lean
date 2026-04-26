import Och.Syntax
import Och.Outcome
import Och.Eval

/-!
# Substitution-based eval and subtype check (benchmarking module)

This module is a parallel implementation of NbE's evaluator + `subCheckVal`
that uses **eager substitution** instead of NbE-style closures. Its sole
purpose is to provide hard performance numbers comparing the two approaches
on a representative workload (see `lean/Och/EvalBench.lean` and
`docs/ideas/eval-subst-vs-env-benchmark.md`).

## Design

- Values are represented as plain `Expr`s (no Val/Closure ADT). When we go
  under a binder, we **substitute** rather than capture-an-env. Each
  substitution walks the body and copies the substituend into every
  occurrence — this is the cost the user wants to measure.

- "Neutral free variables" (the analogue of `Neutral.var depth` in NbE)
  are encoded as `bvar (markerOffset + level)`. We pick a `markerOffset`
  (`100_000_000`) much larger than any bvar that appears in real programs;
  the substitution machinery treats them just like ordinary bvars but they
  remain "stuck" because no enclosing binder rebinds them.

- Evaluation under recursive heads (`fix`/`iota`) is bounded by the same
  `unfBound = 32` schedule that NbE uses, threaded through `unf`.

- The subtype check `subCheckSubst` mirrors `subCheckVal`'s arms 1:1:
  - `.lam, .lam`  — opens both bodies under the same fresh and recurses.
  - `.iota, .iota` / `.fix, .fix` — structural attempt then fallback.
  - `_, .iota` / `_, .fix` — iotaIntro / unfoldFixR.
  - `.iota, _` / `.fix, _` — symmetric ascent paths.
  - neutral-neutral arms via spine compare.

  Comparison uses `Expr` structural equality (via the derived `DecidableEq`,
  no ptrEq fast-path) — this is the cost a substitution-based kernel pays
  on the equality-check hot path.

## Caveats

- This implementation is **soundness-untested**. It's been hand-written to
  mirror `subCheckVal` and produce the same verdict on the BeqBench panel,
  but no proof obligations have been discharged. Discrepancies in verdict
  are flagged by the bench harness.

- The "free-variable encoding via large bvars" works for benchmark inputs
  but isn't a long-term scheme (it would clash with a `Foreign` or `Const`
  primitive that allocates very large bvar indices). Fine for measurement.

- Eval-under-binder cost is roughly equivalent between NbE and subst
  *if you only count the eval pass*; the gap shows up in the **structural
  compare** that subCheckVal does after each open. NbE's closure-sharing
  means two opens of the same closure share their inner sub-Vals, hitting
  `ptrEq`. Substitution copies, so every sub-Expr compare walks fresh trees.
-/

namespace SubstEval

open Outcome

/-- Index offset above which a `bvar` is interpreted as a "free
    neutral variable" (de Bruijn level). Programs in BeqBench
    don't have bvars near this magnitude. -/
def levelOffset : Nat := 100_000_000

/-- Encode a level as a free `bvar`. -/
def levelBvar (level : Nat) : Expr := .bvar (levelOffset + level)

/-- Custom shift that does not touch level-bvars (those at index ≥
    `levelOffset`). Standard `Expr.shift` would shift them, breaking
    their absolute-position semantics. -/
def shiftL (d c : Nat) : Expr → Expr
  | .bvar k =>
      if k >= levelOffset then .bvar k        -- level: do not shift
      else if k < c then .bvar k
      else .bvar (k + d)
  | .lam dom body => .lam (shiftL d c dom) (shiftL d (c + 1) body)
  | .iota ann body => .iota (shiftL d c ann) (shiftL d (c + 1) body)
  | .fix ann body => .fix (shiftL d c ann) (shiftL d (c + 1) body)
  | .letE val body => .letE (shiftL d c val) (shiftL d (c + 1) body)
  | .app f a => .app (shiftL d c f) (shiftL d c a)
  | .asc t ty => .asc (shiftL d c t) (shiftL d c ty)
  | .type => .type
  | .bot => .bot

/-- Custom substitution that does not touch level-bvars.
    Standard `Expr.subst` would decrement level-bvars > j, which is
    semantically wrong (levels are absolute, not relative). Mirror
    `Expr.subst` otherwise. -/
def substL (e : Expr) (j : Nat) (s : Expr) : Expr :=
  match e with
  | .bvar k =>
      if k >= levelOffset then .bvar k             -- level: untouched
      else if k == j then s
      else if k > j then .bvar (k - 1)
      else .bvar k
  | .lam dom body => .lam (substL dom j s) (substL body (j + 1) (shiftL 1 0 s))
  | .app f a => .app (substL f j s) (substL a j s)
  | .asc t ty => .asc (substL t j s) (substL ty j s)
  | .type => .type
  | .bot => .bot
  | .iota ann body => .iota (substL ann j s) (substL body (j + 1) (shiftL 1 0 s))
  | .fix ann body => .fix (substL ann j s) (substL body (j + 1) (shiftL 1 0 s))
  | .letE val body => .letE (substL val j s) (substL body (j + 1) (shiftL 1 0 s))

/-- Open a body under a fresh free variable at the given depth.
    Mirrors `Closure.openFresh fuel depth` in NbE. -/
def openFresh (body : Expr) (depth : Nat) : Expr :=
  substL body 0 (levelBvar depth)

/-- Convert a sub-expression's relative bvars (under `d` opened
    binders) into absolute level-bvars. Bvar k (for k < d) refers
    to the (d-1-k)th opened level. -/
partial def liftToLevels (e : Expr) (d : Nat) : Expr :=
  if d == 0 then e else
    -- Substitute bvars 0..d-1 with level d-1..0 progressively,
    -- starting with the innermost (bvar 0 → level d-1).
    let rec go (e : Expr) (i : Nat) : Expr :=
      if i == d then e
      else go (substL e 0 (levelBvar (d - 1 - i))) (i + 1)
    go e 0

/-- True iff the head of `e` (after walking through application
    spines) is a free-level bvar. Used as the substitution-domain
    analogue of `Val.isNeutral`. -/
def headIsLevel : Expr → Bool
  | .bvar k => k >= levelOffset
  | .app f _ => headIsLevel f
  | _ => false

/-- True iff `e` is a "neutral" — its head is a free level (bvar
    above `levelOffset`) or a stuck application thereof. Mirrors
    `Val.isNeutral`. Lambdas, iotas, fixes, type, bot are NOT
    neutral. -/
def isNeutral : Expr → Bool
  | .bvar k => k >= levelOffset
  | .app f _ => isNeutral f
  | _ => false

/-- A "stuck recursive head" form: a `fix` or `iota` value applied
    to a neutral argument. Mirrors `Neutral.stuckRec` in NbE. -/
def isStuckRec : Expr → Bool
  | .app (.fix _ _) a => isNeutral a
  | .app (.iota _ _) a => isNeutral a
  | _ => false

/-! ## Substitution-based open-term evaluator

Like `concEval` but treats free bvars (those at index ≥ `levelOffset`,
which we use to encode neutral free variables) as values. Carries an
`unf` budget for fix/iota unfolds, mirroring NbE's `unf` schedule.

Result is an `Expr` in head-normal form: lambdas, iotas, fixes, type,
bot, or a neutral spine. -/
def evalSubst (fuel unf : Nat) (e : Expr) : Outcome Expr :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match e with
    | .bvar k =>
      -- Free bvars (≥ levelOffset) are neutral. Bound bvars (<) are stuck —
      -- they shouldn't appear in a closed input, but the eager-substitution
      -- machinery may leave them behind on partial reductions.
      if k >= levelOffset then .ok (.bvar k)
      else .error s!"evalSubst: stuck on bound bvar {k}"
    | .type => .ok .type
    | .bot => .ok .bot
    | .lam _ _ => .ok e
    | .iota _ _ => .ok e
    | .fix _ _ => .ok e
    | .asc t _ => evalSubst fuel unf t
    | .letE val body => do
        let v ← evalSubst fuel unf val
        evalSubst fuel unf (substL body 0 v)
    | .app f a => do
        let f' ← evalSubst fuel unf f
        let a' ← evalSubst fuel unf a
        match f' with
        | .lam _dom body =>
            -- β: substitute argument into body. THIS IS THE COST CENTRE.
            evalSubst fuel unf (substL body 0 a')
        | .iota _ann body =>
            if isNeutral a' || unf == 0 then
              .ok (.app f' a')
            else
              -- ι unfold: substitute self with the ι-value, then re-apply.
              let unfolded := substL body 0 f'
              evalSubst fuel (unf - 1) (.app unfolded a')
        | .fix _ann body =>
            if isNeutral a' || unf == 0 then
              .ok (.app f' a')
            else
              let unfolded := substL body 0 f'
              evalSubst fuel (unf - 1) (.app unfolded a')
        | _ => .ok (.app f' a')

/-- Default unfold bound. Match NbE for apples-to-apples. -/
def unfBound : Nat := 32

/-! ## Subtype check on Expr (substitution-domain)

Mirrors `subCheckVal` arm-by-arm. Uses `Expr` structural equality
(`DecidableEq`-derived `==`) — no `ptrEq` fast-path.

`tyCtx[k]` is the type of the level-bvar at level `k`. Used by
`neutralAscent` to ascend the LHS neutral to its type when the
spine doesn't match. Mirrors NbE's `TyCtx`. -/

abbrev TyCtx := Array Expr

/-- Get the head of a neutral spine (a level bvar). Returns
    `none` if `e` is not a neutral. -/
def neutralHeadLevel : Expr → Option Nat
  | .bvar k => if k >= levelOffset then some (k - levelOffset) else none
  | .app f _ => neutralHeadLevel f
  | _ => none

/-- Walk an application spine, returning the (head, args)
    pair where args are in left-to-right order. -/
def spineArgs : Expr → Expr × List Expr
  | .app f a =>
      let (h, as) := spineArgs f
      (h, as ++ [a])
  | e => (e, [])

mutual
  partial def subCheckSubst (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Outcome Bool :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      -- Force WHNF on both sides. Without this, types stored in tyCtx
      -- and inner doms can be un-evaluated Exprs whose structural
      -- equality doesn't match their fully-reduced form.
      match evalSubst (fuel + 1) unfBound a, evalSubst (fuel + 1) unfBound b with
      | .ok a', .ok b' =>
          if a' == b' then .ok true
          else if seen.any (fun (av, bv) => a' == av && b' == bv) then .ok true
          else if b' == .type then .ok true
          else subCheckSubstMatch fuel tyCtx seen a' b'
      | .outOfFuel, _ | _, .outOfFuel => .outOfFuel
      | .error s, _ | _, .error s => .error s

  partial def subCheckSubstMatch (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Outcome Bool :=
    let depth := tyCtx.size
    match a, b with
    -- Bot ⊑ anything
    | .bot, _ => .ok true
    | .lam domA bodyA, .lam domB bodyB => do
        let contra ← subCheckSubst fuel tyCtx seen domB domA
        if !contra then return false
        let bodyA' := openFresh bodyA depth
        let bodyB' := openFresh bodyB depth
        subCheckSubst fuel (tyCtx.push domA) seen bodyA' bodyB'
    | .iota annA bodyA, .iota annB bodyB =>
        let seen' := (a, b) :: seen
        let structural := do
          let annOk ← subCheckSubst fuel tyCtx seen' annA annB
          if !annOk then return false
          let bodyA' := openFresh bodyA depth
          let bodyB' := openFresh bodyB depth
          subCheckSubst fuel (tyCtx.push annB) seen' bodyA' bodyB'
        match structural with
        | .ok true => .ok true
        | _ => do
          let okAnn ← subCheckSubst fuel tyCtx seen' a annB
          if !okAnn then .ok false
          else do
            let bodyB' := substL bodyB 0 a
            match evalSubst (fuel + 1) unfBound bodyB' with
            | .ok bodyB'' => subCheckSubst fuel tyCtx seen' a bodyB''
            | _ => .ok false
    | .fix annA bodyA, .fix annB bodyB =>
        let seen' := (a, b) :: seen
        let structural := do
          let annOk ← subCheckSubst fuel tyCtx seen' annA annB
          if !annOk then return false
          let bodyA' := openFresh bodyA depth
          let bodyB' := openFresh bodyB depth
          subCheckSubst fuel (tyCtx.push annB) seen' bodyA' bodyB'
        match structural with
        | .ok true => .ok true
        | _ => do
          let unfolded := substL bodyB 0 b
          match evalSubst (fuel + 1) unfBound unfolded with
          | .ok b' => subCheckSubst fuel tyCtx seen' a b'
          | _ => .ok false
    | _, .iota ann bodyB => do
        let seen' := (a, b) :: seen
        let okAnn ← subCheckSubst fuel tyCtx seen' a ann
        if !okAnn then .ok false
        else do
          let bodyB' := substL bodyB 0 a
          match evalSubst (fuel + 1) unfBound bodyB' with
          | .ok bodyB'' => subCheckSubst fuel tyCtx seen' a bodyB''
          | _ => .ok false
    | _, .fix _ann bodyB => do
        let seen' := (a, b) :: seen
        let unfolded := substL bodyB 0 b
        match evalSubst (fuel + 1) unfBound unfolded with
        | .ok b' => subCheckSubst fuel tyCtx seen' a b'
        | _ => .ok false
    | .fix _ann bodyA, _ => do
        let seen' := (a, b) :: seen
        let unfolded := substL bodyA 0 a
        match evalSubst (fuel + 1) unfBound unfolded with
        | .ok a' =>
            if a' == a then .ok false
            else subCheckSubst fuel tyCtx seen' a' b
        | _ => .ok false
    | .iota _ann bodyA, _ => do
        let seen' := (a, b) :: seen
        let unfolded := substL bodyA 0 a
        match evalSubst (fuel + 1) unfBound unfolded with
        | .ok a' =>
            if a' == a then .ok false
            else subCheckSubst fuel tyCtx seen' a' b
        | _ => .ok false
    | _, _ =>
        if isNeutral a && isNeutral b then
          match subCheckSpine fuel tyCtx seen a b with
          | .ok true => .ok true
          | _ => neutralAscent fuel tyCtx seen a b
        else if isNeutral a then
          neutralAscent fuel tyCtx seen a b
        else
          .ok false

  /-- Compare two neutral spines structurally. Heads must be equal
      level-bvars; arguments must be pairwise *equivalent* (any-
      variance). -/
  partial def subCheckSpine (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Outcome Bool :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match a, b with
      | .bvar k1, .bvar k2 =>
          if k1 == k2 && k1 >= levelOffset then .ok true else .ok false
      | .app f1 v1, .app f2 v2 => do
          let hd ← subCheckSpine fuel tyCtx seen f1 f2
          if !hd then return false
          let fwd ← subCheckSubst fuel tyCtx seen v1 v2
          if !fwd then return false
          subCheckSubst fuel tyCtx seen v2 v1
      | _, _ => .ok false

  /-- Synthesise the type of a neutral spine and check against `b`.
      Mirrors NbE's `neutralAscent`. -/
  partial def neutralAscent (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Outcome Bool :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match synthNeutralType fuel tyCtx a with
      | .ok (some ty) => subCheckSubst fuel tyCtx seen ty b
      | _ => .ok false

  /-- Synthesise the type of a neutral. -/
  partial def synthNeutralType (fuel : Nat) (tyCtx : TyCtx)
      (a : Expr) : Outcome (Option Expr) :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match a with
      | .bvar k =>
          if k >= levelOffset then
            let lvl := k - levelOffset
            .ok (tyCtx[lvl]?)
          else .ok none
      | .app f arg => do
          match (← synthNeutralType fuel tyCtx f) with
          | some (.lam _dom retTy) =>
              -- Apply the lambda to `arg` to get the result type:
              -- substitute `arg` for the lam's bound var in retTy.
              let retTy' := substL retTy 0 arg
              match evalSubst (fuel + 1) unfBound retTy' with
              | .ok r => .ok (some r)
              | _ => .ok none
          | _ => .ok none
      | _ => .ok none
end

/-- Top-level entry point analogous to `NbE.subCheck`. -/
def subCheck (fuel : Nat) (a b : Expr) : Outcome Bool := do
  let a' ← evalSubst fuel unfBound a
  let b' ← evalSubst fuel unfBound b
  subCheckSubst fuel #[] [] a' b'

end SubstEval
