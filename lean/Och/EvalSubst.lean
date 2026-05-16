import Och.Syntax
import Och.Outcome
import Och.Eval

/-!
# Substitution-based evaluator and structural subtype check

This module provides Och's primary substitution-based evaluation pipeline:
a head-normal-form evaluator (`evalSubst`) and a structural subtype check
(`subCheck`) that operate directly on `Expr`, never lifting into a
`Val`/`Closure` ADT.

## Status

`evalSubst` is non-`partial` (Lean's elaborator accepts it via lex measure
on `(fuel, unf)`).

The `subCheckSubst` mutual block is non-`partial` as well, with each
function carrying a lex `(fuel, phase)` termination measure. `phase`
distinguishes `subCheckSubst` (phase 0) from `subCheckSubstMatch`
(phase 1): every `subCheckSubst → subCheckSubstMatch` call decrements
`fuel`, and every `subCheckSubstMatch → subCheckSubst` call decrements
phase at the same fuel. All other recursive calls in the block (spine,
ascent, synth, plus self-recursive ones) decrement `fuel` directly.
Equation lemmas (`subCheckSubst.eq_def` etc.) auto-generate, which
the soundness composition in `Soundness/SubCheckSubstSoundness.lean`
relies on.

## Design

- **Values are `Expr`.** No separate `Val`/`Closure` ADT. When applying
  a `λ` to an argument, we substitute the argument into the body. β
  substitutes; ι/fix unfolds substitute their own self-reference into
  their body, then reapply.

- **Free variables are plain `bvar k`** using standard de Bruijn indices.
  When the checker descends under a binder, it extends the context
  (`tyCtx.push domType`) and recurses on the raw body — no substitution
  is performed. Any `bvar k` encountered by `evalSubst` is a free
  variable in the current scope (since evalSubst never goes under
  binders) and is treated as neutral.

- **TyCtx indexing:** `tyCtx` is an Array where we push to the end when
  entering a binder. To look up the type of `bvar k` at the current
  depth, we access `tyCtx[tyCtx.size - 1 - k]`. This means:
    - `tyCtx[0]` = outermost binder's type
    - `tyCtx[tyCtx.size - 1]` = innermost binder's type
    - `bvar 0` (innermost) → `tyCtx[tyCtx.size - 1]`

- **HNF only.** `evalSubst` returns Expr's in head-normal form. It does
  not go under λ-binders during evaluation.

- **`unfBound`** caps fix/ι unfolds, mirroring `NbE.unfBound = 32`.

## Soundness

The previous level-var encoding required a `closeAll` translation to
bridge between the algorithmic level-var representation and the
declarative de Bruijn `Subtype'` relation. By using pure de Bruijn
indices throughout, the algorithmic and declarative representations
now share the same variable encoding, eliminating the `closeAll`
family and its associated sorries.
-/

namespace SubstEval

open Outcome

/-! ## Substitution-based open-term evaluator

Like `concEval` but treats free `bvar`s as neutral values. Carries an
`unf` budget for fix/ι unfolds, mirroring NbE's schedule.

Result is an `Expr` in head-normal form: lambda, iota, fix, type, bot,
or a neutral spine. -/

/-- True iff `e` is a "neutral" — its head is a free `bvar` or a
    stuck application thereof. Lambdas, iotas, fixes, type, bot are
    NOT neutral.

    Exposed (not `private`) so soundness proofs can refer to it. -/
def isNeutral : Expr → Bool
  | .bvar _ => true
  | .app f _ => isNeutral f
  | _ => false

/-- Default unfold bound. Match NbE for apples-to-apples behaviour. -/
def unfBound : Nat := 32

/-- Substitution-based head-normal-form evaluator. Decreasing on
    `(fuel, unf)` lex: every recursive call either decrements `fuel`
    (the outer `match fuel with | _+1 ⇒ …` consumes it) or holds
    `fuel` and decrements `unf` (the iota/fix unfold cases). -/
def evalSubst (fuel unf : Nat) (e : Expr) : Outcome Expr :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match e with
    | .bvar _ =>
      -- All bvars are neutral (free in the current scope, since
      -- evalSubst never goes under binders).
      .ok e
    | .type => .ok .type
    | .bot => .ok .bot
    | .lam _ _ => .ok e
    | .iota _ _ => .ok e
    | .fix _ _ => .ok e
    | .asc t ty => do
        let t' ← evalSubst fuel unf t
        let ty' ← evalSubst fuel unf ty
        .ok (.asc t' ty')
    | .letE val body => do
        let v ← evalSubst fuel unf val
        evalSubst fuel unf (body.subst 0 v)
    | .app f a => do
        let f' ← evalSubst fuel unf f
        let a' ← evalSubst fuel unf a
        match f' with
        | .lam _dom body =>
            -- β: substitute argument into body.
            evalSubst fuel unf (body.subst 0 a')
        | .iota _ann body =>
            if isNeutral a' || unf == 0 then
              .ok (.app f' a')
            else
              -- ι unfold: substitute self with the ι-value, then re-apply.
              let unfolded := body.subst 0 f'
              evalSubst fuel (unf - 1) (.app unfolded a')
        | .fix _ann body =>
            if isNeutral a' || unf == 0 then
              .ok (.app f' a')
            else
              let unfolded := body.subst 0 f'
              evalSubst fuel (unf - 1) (.app unfolded a')
        | .asc inner _ =>
            evalSubst fuel unf (.app inner a')
        | _ => .ok (.app f' a')

/-! ## Subtype check on Expr

Mirrors `subCheckVal` arm-by-arm. Uses `Expr` structural equality
(`DecidableEq`-derived `==`). The type context `tyCtx` stores the
types of free variables: `tyCtx[tyCtx.size - 1 - k]` is the type of
`bvar k`. Used by `neutralAscent` to ascend an LHS neutral to its
type when the spine doesn't match.

The recursion mixes WHNF re-evaluation with structural descent through
binders. Termination is captured by a lex `(fuel, phase)` measure:
`subCheckSubst → subCheckSubstMatch` decrements `fuel`, the reverse
direction decrements phase, and all other recursive calls decrement
`fuel` directly. Equation lemmas auto-generate.
-/

/-- Engine-internal type-context. `tyCtx` is an Array where:
    - Push to the end when entering a binder
    - Look up `bvar k` via `tyCtx[tyCtx.size - 1 - k]`

    Exposed (not `private`) so soundness proofs can refer to it. -/
abbrev TyCtx := Array Expr

/-- Internal: unfold a `.fix` / `.iota` wrapper in `ty` until a
    `.lam` is exposed. Used by `synthNeutralType` to walk a spine
    through types whose Π is wrapped in fix/iota (e.g. `Nat_`'s
    self-eliminator `fix N. ι self:N. λP:..`). The `inhab`
    argument is what to substitute for the ι-self when unfolding
    (typically the spine-head being applied). -/
private def exposePi (fuel : Nat) (inhab : Expr) (ty : Expr) :
    Option Expr :=
  match evalSubst fuel unfBound ty with
  | .ok ty' => go unfBound ty'
  | _ => none
where
  /-- Structurally recursive on the unfold budget `n : Nat`. -/
  go : Nat → Expr → Option Expr
  | 0, e => some e
  | _+1, e@(.lam ..) => some e
  | n+1, e@(.fix _ann body) =>
      match evalSubst fuel 4 (body.subst 0 e) with
      | .ok e' => go n e'
      | _ => none
  | n+1, .iota _ann body =>
      match evalSubst fuel 4 (body.subst 0 inhab) with
      | .ok e' => go n e'
      | _ => none
  | _, .bot => none
  | _, e => some e

mutual
  /-- Top-level subtype check arm. Forces WHNF on both sides, then
      delegates to `subCheckSubstMatch` for case-on-shape.

      Exposed (not `private`) so soundness proofs can refer to it. -/
  def subCheckSubst (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Outcome Bool :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      -- Force WHNF on both sides. Without this, types stored in
      -- tyCtx and inner doms can be un-evaluated Exprs whose
      -- structural equality doesn't match their reduced form.
      match evalSubst (fuel + 1) unfBound a, evalSubst (fuel + 1) unfBound b with
      | .ok a', .ok b' =>
          -- Peel ascriptions asymmetrically before fast paths:
          -- LHS .asc: use annotation (caller sees τ)
          -- RHS .asc: use inner value (content is still e)
          let a'' := match a' with | .asc _ ty => ty | x => x
          let b'' := match b' with | .asc e _ => e | x => x
          if a'' == b'' then .ok true
          else if seen.any (fun (av, bv) => a'' == av && b'' == bv) then .ok true
          else if b'' == .type then .ok true
          else subCheckSubstMatch fuel tyCtx seen a'' b''
      | .outOfFuel, _ | _, .outOfFuel => .outOfFuel
      | .error s, _ | _, .error s => .error s
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)

  /-- The per-shape case-split for `subCheckSubst`. Inputs are assumed
      to be in WHNF (the caller forces it). Exposed for soundness
      proofs. -/
  def subCheckSubstMatch (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Outcome Bool :=
    match a, b with
    -- Bot ⊑ anything ([S-BotL]).
    | .bot, _ => .ok true
    -- λ ⊑ λ: contravariant on domain, covariant on body (under fresh).
    -- Push `domB` (narrower / target) — matches declarative spec.
    | .lam domA bodyA, .lam domB bodyB => do
        let contra ← subCheckSubst fuel tyCtx seen domB domA
        if !contra then return false
        -- Descend into bodies WITHOUT substitution. bvar 0 in the body
        -- refers to the bound variable; extend the context with domB.
        subCheckSubst fuel (tyCtx.push domB) seen bodyA bodyB
    -- ι ⊑ ι: structural attempt then iotaIntro fallback.
    | .iota annA bodyA, .iota annB bodyB =>
        let structural := do
          let annOk ← subCheckSubst fuel tyCtx seen annA annB
          if !annOk then return false
          -- Descend into bodies without substitution.
          subCheckSubst fuel (tyCtx.push annB) seen bodyA bodyB
        match structural with
        | .ok true => .ok true
        | _ => do
          let seen' := (a, b) :: seen
          let okAnn ← subCheckSubst fuel tyCtx seen' a annB
          if !okAnn then .ok false
          else do
            let bodyB' := bodyB.subst 0 a
            match evalSubst (fuel + 1) unfBound bodyB' with
            | .ok bodyB'' => subCheckSubst fuel tyCtx seen' a bodyB''
            | _ => .ok false
    -- fix ⊑ fix: structural attempt then unfold-RHS fallback.
    | .fix annA bodyA, .fix annB bodyB =>
        let structural := do
          let annOk ← subCheckSubst fuel tyCtx seen annA annB
          if !annOk then return false
          -- Descend into bodies without substitution.
          subCheckSubst fuel (tyCtx.push annB) seen bodyA bodyB
        match structural with
        | .ok true => .ok true
        | _ => do
          let seen' := (a, b) :: seen
          let unfolded := bodyB.subst 0 b
          match evalSubst (fuel + 1) unfBound unfolded with
          | .ok b' => subCheckSubst fuel tyCtx seen' a b'
          | _ => .ok false
    -- _ ⊑ ι: iotaIntro.
    | _, .iota ann bodyB => do
        let seen' := (a, b) :: seen
        let okAnn ← subCheckSubst fuel tyCtx seen' a ann
        if !okAnn then .ok false
        else do
          let bodyB' := bodyB.subst 0 a
          match evalSubst (fuel + 1) unfBound bodyB' with
          | .ok bodyB'' => subCheckSubst fuel tyCtx seen' a bodyB''
          | _ => .ok false
    -- _ ⊑ fix: unfoldFixR.
    | _, .fix _ann bodyB => do
        -- Neutral-LHS short-circuit: if `a` is a neutral whose ascended
        -- type via tyCtx is structurally `b`, accept immediately.
        if isNeutral a then
          match synthNeutralType fuel tyCtx a with
          | .ok (some ty) =>
              if ty == b then .ok true
              else
                let seen' := (a, b) :: seen
                let unfolded := bodyB.subst 0 b
                match evalSubst (fuel + 1) unfBound unfolded with
                | .ok b' => subCheckSubst fuel tyCtx seen' a b'
                | _ => .ok false
          | _ =>
              let seen' := (a, b) :: seen
              let unfolded := bodyB.subst 0 b
              match evalSubst (fuel + 1) unfBound unfolded with
              | .ok b' => subCheckSubst fuel tyCtx seen' a b'
              | _ => .ok false
        else
          let seen' := (a, b) :: seen
          let unfolded := bodyB.subst 0 b
          match evalSubst (fuel + 1) unfBound unfolded with
          | .ok b' => subCheckSubst fuel tyCtx seen' a b'
          | _ => .ok false
    -- fix ⊑ _: unfoldFixL.
    | .fix _ann bodyA, _ => do
        let seen' := (a, b) :: seen
        let unfolded := bodyA.subst 0 a
        match evalSubst (fuel + 1) unfBound unfolded with
        | .ok a' =>
            if a' == a then .ok false
            else subCheckSubst fuel tyCtx seen' a' b
        | _ => .ok false
    -- ι ⊑ _: iotaElim.
    | .iota _ann bodyA, _ => do
        let seen' := (a, b) :: seen
        let unfolded := bodyA.subst 0 a
        match evalSubst (fuel + 1) unfBound unfolded with
        | .ok a' =>
            if a' == a then .ok false
            else subCheckSubst fuel tyCtx seen' a' b
        | _ => .ok false
    -- Neutrals: try spine-compare; if that fails (or for one-sided
    -- neutrals), ascend to the LHS neutral's type and recurse.
    | _, _ =>
        if isNeutral a && isNeutral b then
          match subCheckSpine fuel tyCtx seen a b with
          | .ok true => .ok true
          | _ => neutralAscent fuel tyCtx seen a b
        else if isNeutral a then
          neutralAscent fuel tyCtx seen a b
        else
          .ok false
  termination_by (fuel, 1)
  decreasing_by all_goals (simp_wf; omega)

  /-- Compare two neutral spines structurally. Heads must be equal
      `bvar`s; arguments must be pairwise *equivalent* (any-
      variance). Exposed for soundness proofs. -/
  def subCheckSpine (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Outcome Bool :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match a, b with
      | .bvar k1, .bvar k2 =>
          if k1 == k2 then .ok true else .ok false
      | .app f1 v1, .app f2 v2 => do
          let hd ← subCheckSpine fuel tyCtx seen f1 f2
          if !hd then return false
          let fwd ← subCheckSubst fuel tyCtx seen v1 v2
          if !fwd then return false
          subCheckSubst fuel tyCtx seen v2 v1
      | _, _ => .ok false
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)

  /-- Synthesise the type of a neutral spine and check against `b`.
      Mirrors NbE's `neutralAscent`. Exposed for soundness proofs. -/
  def neutralAscent (fuel : Nat) (tyCtx : TyCtx)
      (seen : List (Expr × Expr)) (a b : Expr) : Outcome Bool :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match synthNeutralType fuel tyCtx a with
      | .ok (some ty) => subCheckSubst fuel tyCtx seen ty b
      | _ => .ok false
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)

  /-- Synthesise the type of a neutral. Walks the spine, looking up
      head bvars in `tyCtx` (via de Bruijn index) and applying argument
      types to function types via `Expr.subst`. When the synthesised
      type at a spine step is a `.fix` or `.iota`, unfold it via
      `exposePi` to expose the underlying `.lam` and continue.
      A `.fix` at the spine head ascends to its annotation.
      Exposed for soundness proofs. -/
  def synthNeutralType (fuel : Nat) (tyCtx : TyCtx)
      (a : Expr) : Outcome (Option Expr) :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match a with
      | .bvar k =>
          -- Look up bvar k in the context. tyCtx stores types
          -- with push-to-end convention: tyCtx[tyCtx.size - 1 - k]
          -- is the type of bvar k.
          let idx := tyCtx.size - 1 - k
          if k < tyCtx.size then
            match tyCtx[idx]? with
            | some ty =>
                -- Shift the type up by (k+1) to account for the
                -- binders between where it was stored and current scope.
                -- This matches the declarative [S-Var] rule:
                --   Γ.get? k = some τ → bvar k ⊑ τ.shift (k+1)
                .ok (some (ty.shift (k + 1) 0))
            | none => .ok none
          else .ok none
      | .fix ann _ =>
          -- A fix's type-via-Refl is itself, but for spine walking
          -- we want the *function-type* under which arguments
          -- consume — that's the annotation.
          match evalSubst (fuel + 1) unfBound ann with
          | .ok ann' => .ok (some ann')
          | _ => .ok none
      | .app f arg => do
          match (← synthNeutralType fuel tyCtx f) with
          | some ty =>
              -- Expose a Π via fix/iota unfolding if needed. The
              -- inhabitant for ι-unfolding is `f` (the spine head
              -- that's being applied), since that's what
              -- structurally inhabits the ι annotation here.
              match exposePi fuel f ty with
              | some (.lam _dom retTy) =>
                  let retTy' := retTy.subst 0 arg
                  match evalSubst (fuel + 1) unfBound retTy' with
                  | .ok r => .ok (some r)
                  | _ => .ok none
              | _ => .ok none
          | _ => .ok none
      | _ => .ok none
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)
end

/-- Structural subtype check on closed `Expr`s: WHNF both sides,
    then descend through `subCheckSubst`. Public so `TyCheck.typeCheck`
    can call it on conversion goals; the `subCheckSubst` mutual
    block stays private. -/
def subCheck (fuel : Nat) (a b : Expr) : Outcome Bool := do
  let a' ← evalSubst fuel unfBound a
  let b' ← evalSubst fuel unfBound b
  subCheckSubst fuel #[] [] a' b'

/-! ## Open-context API for `TyCheck` and `API`

The bidirectional type-checker and the synth walk need:

  - a way to substitute a value for the outermost binder (`substTop`),
  - a way to compare two types in a non-empty type context (`subCheckOpen`).

In the pure de Bruijn regime, binder-opening is trivial: we just recurse
on the raw body with an extended context. No fresh variable substitution
is needed. `freshLevelVar` is kept as a compatibility shim that returns
`bvar (depth)` — this represents the outermost free variable when the
context has `depth + 1` entries after a push.
-/

/-- Compatibility shim: in the old level-var regime, this returned
    `bvar (levelOffset + level)`. In pure de Bruijn, the "fresh variable"
    at depth `d` (after pushing to make context size `d+1`) is simply
    `bvar 0` — the innermost binder. This function is retained for
    callers that need to construct a reference to a specific context
    entry by its push-order index (level). The corresponding de Bruijn
    index is `currentDepth - 1 - level`. -/
def freshLevelVar (level : Nat) : Expr := .bvar level

/-- Substitute a value for the outermost binder of `body`. Uses
    standard de Bruijn substitution. -/
def substTop (body : Expr) (value : Expr) : Expr :=
  body.subst 0 value

/-- Subtype check in a non-empty type context. Forces WHNF on both
    sides, then delegates to the structural engine. -/
def subCheckOpen (fuel : Nat) (tyCtx : Array Expr) (a b : Expr) :
    Outcome Bool := do
  let a' ← evalSubst fuel unfBound a
  let b' ← evalSubst fuel unfBound b
  subCheckSubst fuel tyCtx [] a' b'

/-- Walk a neutral spine to compute its declarative type, looking
up bvars in `tyCtx` and applying argument types through `Π` bodies
via `Expr.subst`. Public mirror of the internal `synthNeutralType`.

`Och.synth` calls this from its `.app` arm to recover the Π type
of a neutral function head.

- `.ok (some ty)` — neutral head ascended to type `ty` (in WHNF).
- `.ok none` — `a` is not a neutral, or its head is unbound.
- `.outOfFuel` — fuel exhausted. -/
def neutralType (fuel : Nat) (tyCtx : Array Expr) (a : Expr) :
    Outcome (Option Expr) :=
  synthNeutralType fuel tyCtx a

/-! ## Π-exposure helper

`Och.synth` (`Och/API.lean`) needs to destructure the synthesised
type/value of an applied head as a `.lam dom body` (a Π). When the
head is a `.fix`/`.iota`, we unfold the wrapper one or more times
to expose the underlying Π. -/

/-- Unfold a `.fix` / `.iota` wrapper in `ty` until a `.lam`
(Π) is exposed, returning the Π. The `inhab` argument is what
to substitute for the `ι`-self when unfolding `.iota` (= the
*inhabitant* whose type we're computing). For `.fix`, the self
is substituted with the fix itself (μ-unfold).

- `some (.lam dom body)` — Π exposed.
- `some other` — non-Π head after WHNF.
- `none` — `.bot` or evaluation failure. -/
def whnfPi (fuel : Nat) (inhab : Expr) (ty : Expr) : Option Expr :=
  match evalSubst fuel unfBound ty with
  | .ok ty' => go unfBound ty'
  | _ => none
where
  go : Nat → Expr → Option Expr
  | 0, e => some e
  | _+1, e@(.lam ..) => some e
  | n+1, e@(.fix _ann body) =>
      match evalSubst fuel 4 (body.subst 0 e) with
      | .ok e' => go n e'
      | _ => none
  | n+1, .iota _ann body =>
      match evalSubst fuel 4 (body.subst 0 inhab) with
      | .ok e' => go n e'
      | _ => none
  | _, .bot => none
  | _, e => some e

end SubstEval
