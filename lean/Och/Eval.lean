import Och.Syntax
import Och.Outcome

/-!
# Och concrete evaluation

`concEval` is the substitution-based CBV big-step evaluator for closed
terms. Lambdas and ι/fix binders are values (bodies not evaluated until
applied). `(e : τ)` erases to `e`. ι/fix unroll only when applied (the
mu-app dispatch: substitute the self-reference, then re-apply).

This is the *runtime* evaluator targeted by `concEval_preservation` in
`Soundness.lean`.

## Legacy checker removed

The Expr-domain abstract evaluator (`absEval`/`subCheckNF`/`neutralType`/
`subCheck`/`absEvalVal`/`NfExpr`/`TyCtx`) was removed at this commit. It
predated the NbE/Val-domain pipeline and was kept only for the
divergence sweep in `SoundnessAudit.lean`, which had served its purpose
(it found A1–A8; the only remaining divergence was the documented A6
incompleteness). The Phase-2 soundness theorem targets `NbE.subCheckVal`
(`SubCheckVal.lean`) via `NbE.typeCheck` (`TyCheck.lean`); maintaining a
parallel checker was a tax with no remaining benefit. The last revision
with the legacy checker is `38d1031`; the original combined fuel-mono
scaffold is at `f82fbfc`.
-/

open Expr

/-! ## Except instances for native_decide

These let `native_decide` discharge goals of the form
`NbE.subCheck … = .ok true` / `NbE.typeCheck … = .ok true`. Kept here
because most `Std/` modules import this file. -/

instance {ε : Type} {α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) := fun a b =>
  match a, b with
  | .ok a, .ok b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro h2; cases h2; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (by rw [h]) else isFalse (by intro h2; cases h2; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

instance {ε : Type} {α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq a b := match a, b with
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

instance {ε : Type} {α : Type} [Repr ε] [Repr α] : Repr (Except ε α) where
  reprPrec x n := match x with
    | .ok a => Repr.addAppParen (".ok " ++ reprPrec a 1) n
    | .error e => Repr.addAppParen (".error " ++ reprPrec e 1) n

/-! ## concEval -/

/-- Concrete evaluator. Standard call-by-value lambda calculus with substitution.

    Lambdas and ι/fix are values — their bodies are NOT evaluated until applied.
    Uses substitution for beta-reduction. Operates on closed terms only
    (free bvars are stuck: `.error`). ι/fix is only unrolled when it appears in function
    position (substitute self-reference, then re-apply).

    Returns `Outcome Expr`: `.outOfFuel` is the fuel-exhaustion case;
    `.error` covers genuine stuckness (free variable, applying to Bot, etc.). -/
def concEval (fuel : Nat) (e : Expr) : Outcome Expr :=
  match fuel with
  | 0 => .outOfFuel
  | fuel + 1 =>
    match e with
    | .bvar k => .error s!"concEval: stuck on free bvar {k}"
    | .lam _ _ | .type | .bot | .iota _ _ | .fix _ => .ok e -- direct values
    | .app f a =>
      match concEval fuel f, concEval fuel a with
      | .ok (.lam _dom body), .ok aVal =>
        -- Beta-reduce via substitution
        concEval fuel (body.subst 0 aVal)
      | .ok (.iota ann body), .ok aVal =>
        -- iota in function position: unroll self-reference, then re-apply
        concEval fuel (.app (body.subst 0 (.iota ann body)) aVal)
      | .ok (.fix body), .ok aVal =>
        -- fix in function position: unroll self-reference, then re-apply
        concEval fuel (.app (body.subst 0 (.fix body)) aVal)
      | .ok _fVal, .ok _aVal =>
        .error s!"concEval: application of non-function"
      | .outOfFuel, _ | _, .outOfFuel => .outOfFuel
      | .error s, _ | _, .error s => .error s

/-! ## Fuel monotonicity -/

/-- `concEval` preserves closedness: evaluating a closed term
produces a closed term. Needed to thread closedness through the
`concEval_equiv` → `Equiv.subst_resp_closed` chain, which is
the pragmatic route for closing `Equiv.shift`'s nil-Γ sorry
(see DECISION-LOG 2026-04-21).

Proof by induction on fuel + case on `e`. Uses
`Expr.subst_closedAt_gen` at `j=0, n=0` for the β-binder
cases to show `(body.subst 0 v).closedAt 0` from
`body.closedAt 1` and `v.closedAt 0`. -/
theorem concEval_closedAt {n : Nat} {e v : Expr}
    (hcl : e.closedAt 0 = true)
    (h : concEval n e = .ok v) : v.closedAt 0 = true := by
  sorry

theorem concEval_fuel_mono {n : Nat} {e v : Expr}
    (h : concEval n e = .ok v) : concEval (n + 1) e = .ok v := by
  sorry

/-! ## concEval shape lemmas

concEval never produces bvar at the top level. This is a structural
invariant: the base cases (lam, type, ι, fix) never produce them, and the
recursive cases just propagate inner results. The catch-all (neutral app)
produces app. -/

/-- concEval never produces a bare variable at the top level. -/
theorem concEval_not_bvar {fuel : Nat} {e : Expr} {k : Nat}
    (h : concEval fuel e = .ok (.bvar k)) : False := by
  sorry

/-- Concrete normal form: the shape of concEval outputs.
    Values are lam/type/iota/fix (base values) or neutral applications where
    the function is not lam/iota/fix (not a redex) and sub-expressions are ConcNF. -/
inductive ConcNF : Expr → Prop
  | lam (dom body : Expr) : ConcNF (.lam dom body)
  | type : ConcNF .type
  | bot : ConcNF .bot
  | iota (ann body : Expr) : ConcNF (.iota ann body)
  | fix (body : Expr) : ConcNF (.fix body)
  | app (f a : Expr) : ConcNF f → ConcNF a →
      (match f with | .lam _ _ | .iota _ _ | .fix _ => False | _ => True) → ConcNF (.app f a)

/-- concEval always produces ConcNF values. -/
theorem concEval_ConcNF {fuel : Nat} {e v : Expr}
    (h : concEval fuel e = .ok v) : ConcNF v := by
  sorry

/-- ConcNF values are idempotent under concEval: if concEval succeeds on
    a ConcNF value, it returns the same value. This is because ConcNF values
    have no redexes (no beta-reducible lam-app or mu-app). -/
theorem ConcNF_concEval_idem {v v' : Expr} {fuel : Nat}
    (hv : ConcNF v) (h : concEval fuel v = .ok v') : v' = v := by
  sorry

/-- ConcNF implies the old isConcreteVal-or-app pattern: not bvar. -/
theorem ConcNF.not_bvar {v : Expr} (h : ConcNF v) : ∀ k, v ≠ .bvar k := by
  intro k; cases h <;> intro heq <;> cases heq
