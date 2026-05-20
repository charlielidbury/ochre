import Och.Syntax
import Och.Outcome
import Och.Eval
import Och.Subtyping

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
    | .fix _ => .ok e
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
        | .fix body =>
            if isNeutral a' || unf == 0 then
              .ok (.app f' a')
            else
              let unfolded := body.subst 0 f'
              evalSubst fuel (unf - 1) (.app unfolded a')
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

/-- Engine-internal type-context. `Γ[k]` is the type of `bvar k`.
    Stored as `Ctx = List Expr` in de Bruijn order: `Γ[0]` =
    innermost binder, matching `Subtype'`'s context directly.
    When entering a binder, prepend: `domV :: Γ`.
    Exposed (not `private`) so soundness proofs can refer to it. -/
abbrev TyCtx := Ctx

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
  | n+1, e@(.fix body) =>
      match evalSubst fuel 4 (body.subst 0 e) with
      | .ok e' => go n e'
      | _ => none
  | n+1, .iota _ann body =>
      match evalSubst fuel 4 (body.subst 0 inhab) with
      | .ok e' => go n e'
      | _ => none
  | _, .bot => none
  | _, e => some e

/-! ### Structural subtype checker -/

mutual
  /-- Top-level subtype check arm (Bool version). Forces WHNF on both
      sides, then delegates to `subCheckSubstMatch`. -/
  def subCheckSubst (fuel : Nat) (tyCtx : TyCtx)
      (seen : Seen) (a b : Expr) : Outcome Bool :=
    match fuel with
    | 0 => .outOfFuel
    | fuel + 1 =>
      match evalSubst (fuel + 1) unfBound a, evalSubst (fuel + 1) unfBound b with
      | .ok a', .ok b' =>
          if a' == b' then .ok true
          else if seen.any (fun (d, av, bv) => d == tyCtx.length && a' == av && b' == bv) then .ok true
          else if b' == .type then .ok true
          else subCheckSubstMatch fuel tyCtx seen a' b'
      | .outOfFuel, _ | _, .outOfFuel => .outOfFuel
      | .error s, _ | _, .error s => .error s
  termination_by (fuel, 0)
  decreasing_by all_goals (simp_wf; omega)

  /-- Per-shape case-split (Bool version). -/
  def subCheckSubstMatch (fuel : Nat) (tyCtx : TyCtx)
      (seen : Seen) (a b : Expr) : Outcome Bool :=
    match a, b with
    | .bot, _ => .ok true
    | .lam _domA _bodyA, .lam domB bodyB => do
        let contra ← subCheckSubst fuel tyCtx seen domB _domA
        if !contra then return false
        subCheckSubst fuel (domB :: tyCtx) seen _bodyA bodyB
    | .iota _annA _bodyA, .iota annB bodyB =>
        let seen' := (tyCtx.length, a, b) :: seen
        let structural := do
          -- Self-referential guard: if the annotations evaluate to
          -- the same terms as a/b, the structural check would repeat
          -- the original query. Short-circuit via the seen hypothesis.
          match evalSubst (fuel + 1) unfBound _annA,
                evalSubst (fuel + 1) unfBound annB with
          | .ok annA', .ok annB' =>
            if annA' == a && annB' == b then return true
            else pure ()
          | _, _ => pure ()
          let annOk ← subCheckSubst fuel tyCtx seen' _annA annB
          if !annOk then return false
          subCheckSubst fuel (annB :: tyCtx) seen' _bodyA bodyB
        match structural with
        | .ok true => .ok true
        | _ => do
          let okAnn ← subCheckSubst fuel tyCtx seen' a annB
          if !okAnn then .ok false
          else do
            let bodyB' := bodyB.subst 0 a
            match evalSubst (fuel + 1) unfBound bodyB' with
            | .ok bodyB'' => subCheckSubst fuel tyCtx seen' a bodyB''
            | _ => .ok false
    | .fix _bodyA, .fix bodyB =>
        let seen' := (tyCtx.length, a, b) :: seen
        let structural := do
          subCheckSubst fuel (b :: tyCtx) seen' _bodyA bodyB
        match structural with
        | .ok true => .ok true
        | _ => do
          let unfolded := bodyB.subst 0 b
          match evalSubst (fuel + 1) unfBound unfolded with
          | .ok b' => subCheckSubst fuel tyCtx seen' a b'
          | _ => .ok false
    | _, .iota ann bodyB => do
        let seen' := (tyCtx.length, a, b) :: seen
        let okAnn ← subCheckSubst fuel tyCtx seen' a ann
        if !okAnn then
          -- Iota-intro failed (a ⊄ ann). For neutral `a`, fall back
          -- to ascent: check type_of(a) ⊑ b. This covers e.g.
          -- `i : Fin(succ_ p) ⊑ Fin(succ_ p)` where the iota's
          -- annotation (Nat_) is wider than Fin and the direct path
          -- `a ⊑ Nat_` fails, but `Fin(succ_ p) ⊑ Fin(succ_ p)`
          -- holds reflexively.
          -- Uses `seen` (not `seen'`) so the soundness proof can
          -- derive Subtype' S directly without the iota guard entry.
          neutralAscent fuel tyCtx seen a b
        else do
          let bodyB' := bodyB.subst 0 a
          match evalSubst (fuel + 1) unfBound bodyB' with
          | .ok bodyB'' => subCheckSubst fuel tyCtx seen' a bodyB''
          | _ => .ok false
    | _, .fix bodyB => do
        if isNeutral a then
          match synthNeutralType fuel tyCtx a with
          | .ok (some ty) =>
              if ty == b then .ok true
              else
                let seen' := (tyCtx.length, a, b) :: seen
                let unfolded := bodyB.subst 0 b
                match evalSubst (fuel + 1) unfBound unfolded with
                | .ok b' => subCheckSubst fuel tyCtx seen' a b'
                | _ => .ok false
          | _ =>
              let seen' := (tyCtx.length, a, b) :: seen
              let unfolded := bodyB.subst 0 b
              match evalSubst (fuel + 1) unfBound unfolded with
              | .ok b' => subCheckSubst fuel tyCtx seen' a b'
              | _ => .ok false
        else
          let seen' := (tyCtx.length, a, b) :: seen
          let unfolded := bodyB.subst 0 b
          match evalSubst (fuel + 1) unfBound unfolded with
          | .ok b' => subCheckSubst fuel tyCtx seen' a b'
          | _ => .ok false
    | .fix bodyA, _ => do
        let seen' := (tyCtx.length, a, b) :: seen
        let unfolded := bodyA.subst 0 a
        match evalSubst (fuel + 1) unfBound unfolded with
        | .ok a' =>
            if a' == a then .ok false
            else subCheckSubst fuel tyCtx seen' a' b
        | _ => .ok false
    | .iota _ann bodyA, _ => do
        let seen' := (tyCtx.length, a, b) :: seen
        let unfolded := bodyA.subst 0 a
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
  termination_by (fuel, 1)
  decreasing_by all_goals (simp_wf; omega)

  /-- Compare two neutral spines structurally (Bool version). -/
  def subCheckSpine (fuel : Nat) (tyCtx : TyCtx)
      (seen : Seen) (a b : Expr) : Outcome Bool :=
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

  /-- Synthesise the type of a neutral spine and check against `b`
      (Bool version). -/
  def neutralAscent (fuel : Nat) (tyCtx : TyCtx)
      (seen : Seen) (a b : Expr) : Outcome Bool :=
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
          match tyCtx.get? k with
          | some ty =>
              .ok (some (ty.shift (k + 1) 0))
          | none => .ok none
      | .fix body =>
          match evalSubst (fuel + 1) unfBound (body.subst 0 (.fix body)) with
          | .ok unfolded => .ok (some unfolded)
          | _ => .ok none
      | .app f arg => do
          match (← synthNeutralType fuel tyCtx f) with
          | some ty =>
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
  subCheckSubst fuel [] [] a' b'

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
def subCheckOpen (fuel : Nat) (tyCtx : TyCtx) (a b : Expr) :
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
def neutralType (fuel : Nat) (tyCtx : TyCtx) (a : Expr) :
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
  | n+1, e@(.fix body) =>
      match evalSubst fuel 4 (body.subst 0 e) with
      | .ok e' => go n e'
      | _ => none
  | n+1, .iota _ann body =>
      match evalSubst fuel 4 (body.subst 0 inhab) with
      | .ok e' => go n e'
      | _ => none
  | _, .bot => none
  | _, e => some e

/-- The `go` helper of `exposePi` computes the same result as `whnfPi.go`. -/
private theorem exposePi_go_eq_whnfPi_go (fuel : Nat) (inhab : Expr)
    : ∀ (n : Nat) (e : Expr),
      exposePi.go fuel inhab n e = whnfPi.go fuel inhab n e := by
  intro n
  induction n with
  | zero => intro e; cases e <;> rfl
  | succ m ih =>
    intro e
    match e with
    | .lam _ _ => rfl
    | .fix body =>
      simp only [exposePi.go, whnfPi.go]
      match evalSubst fuel 4 (body.subst 0 (.fix body)) with
      | .ok e' => exact ih e'
      | .outOfFuel => rfl
      | .error _ => rfl
    | .iota _ann body =>
      simp only [exposePi.go, whnfPi.go]
      match evalSubst fuel 4 (body.subst 0 inhab) with
      | .ok e' => exact ih e'
      | .outOfFuel => rfl
      | .error _ => rfl
    | .bot => rfl
    | .bvar _ => rfl
    | .type => rfl
    | .app _ _ => rfl

/-- `exposePi` (private, used by `synthNeutralType`) computes the same
result as `whnfPi` (public). Proved inside the section where
`exposePi` is in scope, exposed for soundness proofs that need
to reason about `synthNeutralType`'s internal call to `exposePi`. -/
theorem exposePi_eq_whnfPi (fuel : Nat) (inhab ty : Expr) :
    exposePi fuel inhab ty = whnfPi fuel inhab ty := by
  unfold exposePi whnfPi
  match evalSubst fuel unfBound ty with
  | .ok ty' => exact exposePi_go_eq_whnfPi_go fuel inhab unfBound ty'
  | .outOfFuel => rfl
  | .error _ => rfl

end SubstEval
