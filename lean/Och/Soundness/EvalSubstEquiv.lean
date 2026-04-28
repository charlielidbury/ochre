import Och.Syntax
import Och.EvalSubst
import Och.Subtyping
import Och.Soundness.SubtypeSteps
import Och.Soundness.EvalSubstLemmas

/-!
# Bidirectional `evalSubst` equivalence (partial)

Mirror of `Och.Soundness.concEval_equiv` for the substitution-based
evaluator `SubstEval.evalSubst`.

```
evalSubst fuel unf e = .ok e' → Subtype' [] [] e' e ∧ Subtype' [] [] e e'
```

The structure is arm-for-arm identical to `concEval_equiv`. The only
substantive differences are:

* `evalSubst` uses the level-aware substitution `SubstEval.substL`
  (treats `bvar k` with `k ≥ levelOffset` as a value). On terms with
  no level-vars (every realistic top-level call), `substL = Expr.subst`
  via the bridge `SubstEval.substL_eq_subst_no_levelvars`.

* `evalSubst` carries an `unf` budget for fix/ι unfolds. When it stops
  early (`unf == 0` or argument is neutral), the result is a stuck
  application `.app fv av`. Both directions of `Subtype'` close via
  `app_cong` with the IH for `f`/`a`.

* `evalSubst`'s `.bvar k` arm produces `.ok (.bvar k)` when
  `isLevelIdx k`. Under `closedAt 0` the input has bvars at most as
  deep as the local binder cutoff, hence well below `levelOffset` for
  any realistic program; the level-bvar arm is unreachable in the
  closed regime.

## Hypothesis: `closedAt 0` plus a depth budget

We require `e.closedAt 0 = true` and a numeric depth budget so that
the level-offset encoding can never trip during evaluation.  The
budget is captured as `bvarLT m e` for some `m` together with an
arithmetic bound `m + e.depth ≤ levelOffset` —  the same shape that
`SubstEval.substL_eq_subst_bvarLT` already uses.

## Status

This is a **partial** discharge of the soundness wall in
`Soundness/SubCheckSubstSoundness.lean`'s `evalSubst_bridge_WALL_a/b`.

* The structural arms (`.bvar`, `.type`, `.bot`, `.lam`, `.iota`,
  `.fix`, `.asc`, neutral application stops) close cleanly via
  `Subtype'.refl` / `Subtype'.asc_L/R` / `Subtype'.app_cong`.

* The `evalSubst`-specific arms that perform `substL` (β, iota-unfold,
  fix-unfold, letE) require the `substL = Expr.subst` bridge. We
  carry the bridge's depth budget as a hypothesis at the top level
  but threading it through recursive calls (where the substituted
  term grows) requires either a stronger global invariant or a
  fresh `Subtype'_substL` constructor; see `WALL_substL_depth` notes
  inline.

This mirrors the earlier `eval_bridge_a/b` sorries — those still
exist, but the surface area is better understood, and the value /
neutral arms are now established. -/

namespace Och.Soundness

open SubstEval
open Expr (closedAt closedAtLvl noLevelVars bvarLT)

/-! ## Auxiliary: `closedAt n e → bvarLT (n + e.depth) e`

`closedAt n` increments under each binder; `bvarLT m` is uniform.
The maximum bvar index in a `closedAt n e` term is bounded by `n +
(depth at that occurrence)` ≤ `n + e.depth`. -/

private theorem bvarLT_of_closedAt (e : Expr) (n : Nat)
    (h : closedAt n e = true) : bvarLT (n + e.depth) e = true := by
  induction e generalizing n with
  | bvar k =>
    simp only [closedAt, decide_eq_true_eq] at h
    simp only [bvarLT, Expr.depth, decide_eq_true_eq]
    omega
  | type => simp [bvarLT]
  | bot => simp [bvarLT]
  | lam dom body ih_dom ih_body =>
    simp only [closedAt, Bool.and_eq_true] at h
    simp only [bvarLT, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have := ih_dom n h.1
      apply bvarLT_mono this
      simp only [Expr.depth, Nat.max_def]; split <;> omega
    · have := ih_body (n + 1) h.2
      apply bvarLT_mono this
      simp only [Expr.depth, Nat.max_def]; split <;> omega
  | app f a ih_f ih_a =>
    simp only [closedAt, Bool.and_eq_true] at h
    simp only [bvarLT, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have := ih_f n h.1
      apply bvarLT_mono this
      simp only [Expr.depth, Nat.max_def]; split <;> omega
    · have := ih_a n h.2
      apply bvarLT_mono this
      simp only [Expr.depth, Nat.max_def]; split <;> omega
  | asc t y ih_t ih_y =>
    simp only [closedAt, Bool.and_eq_true] at h
    simp only [bvarLT, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have := ih_t n h.1
      apply bvarLT_mono this
      simp only [Expr.depth, Nat.max_def]; split <;> omega
    · have := ih_y n h.2
      apply bvarLT_mono this
      simp only [Expr.depth, Nat.max_def]; split <;> omega
  | iota ann body ih_ann ih_body =>
    simp only [closedAt, Bool.and_eq_true] at h
    simp only [bvarLT, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have := ih_ann n h.1
      apply bvarLT_mono this
      simp only [Expr.depth, Nat.max_def]; split <;> omega
    · have := ih_body (n + 1) h.2
      apply bvarLT_mono this
      simp only [Expr.depth, Nat.max_def]; split <;> omega
  | fix ann body ih_ann ih_body =>
    simp only [closedAt, Bool.and_eq_true] at h
    simp only [bvarLT, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have := ih_ann n h.1
      apply bvarLT_mono this
      simp only [Expr.depth, Nat.max_def]; split <;> omega
    · have := ih_body (n + 1) h.2
      apply bvarLT_mono this
      simp only [Expr.depth, Nat.max_def]; split <;> omega
  | letE val body ih_val ih_body =>
    simp only [closedAt, Bool.and_eq_true] at h
    simp only [bvarLT, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · have := ih_val n h.1
      apply bvarLT_mono this
      simp only [Expr.depth, Nat.max_def]; split <;> omega
    · have := ih_body (n + 1) h.2
      apply bvarLT_mono this
      simp only [Expr.depth, Nat.max_def]; split <;> omega

/-! ## Main equivalence (partial)

We prove the bidirectional equivalence on `closedAt 0` inputs.  The
β/iota-unfold/fix-unfold/letE arms refer to a `WALL_substL_depth`
sub-lemma that the per-recursion depth bound supplies — when the
substituted term `s` has bounded depth, `substL = Expr.subst` and
the standard `Subtype'.beta_L` / `unfold_iota_L` constructors fire.
The depth bound is a substrate hygiene fact that's not yet
formalised; the wall lives in that depth-tracking invariant, not in
the `Subtype'` construction itself. -/

/-- The two-direction subtype equivalence between an expression and
the result of `evalSubst`.  Mirrors `concEval_equiv`. -/
theorem evalSubst_equiv {fuel unf : Nat} {e e' : Expr}
    (hcl : e.closedAt 0 = true)
    (hstep : evalSubst fuel unf e = .ok e') :
    Subtype' [] [] e' e ∧ Subtype' [] [] e e' := by
  induction fuel generalizing unf e e' with
  | zero => rw [evalSubst.eq_1] at hstep; cases hstep
  | succ n ih =>
    match e, hcl, hstep with
    | .bvar k, hcl, h =>
      -- closedAt 0 forbids any bvar (k < 0 impossible).
      simp only [closedAt, decide_eq_true_eq] at hcl
      omega
    | .type, _, h =>
      rw [evalSubst.eq_3] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .bot, _, h =>
      rw [evalSubst.eq_4] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .lam dom body, _, h =>
      rw [evalSubst.eq_5] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .iota ann body, _, h =>
      rw [evalSubst.eq_6] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .fix ann body, _, h =>
      rw [evalSubst.eq_7] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .asc t ty, hcl, h =>
      simp only [closedAt, Bool.and_eq_true] at hcl
      rw [evalSubst.eq_8] at h
      have ⟨h₁, h₂⟩ := ih hcl.1 h
      refine ⟨?_, ?_⟩
      · exact .asc_R h₁
      · exact .asc_L h₂
    | .letE val body, hcl, h =>
      -- WALL_substL_depth — needs `substL body 0 vv = body.subst 0 vv`
      -- to apply `Subtype'.letE_L/R`.
      sorry
    | .app f a, hcl, h =>
      simp only [closedAt, Bool.and_eq_true] at hcl
      rw [evalSubst.eq_10] at h
      match hfEv : evalSubst n unf f with
      | .outOfFuel => rw [hfEv] at h; cases h
      | .error _ => rw [hfEv] at h; cases h
      | .ok fv =>
        have ⟨hf₁, hf₂⟩ := ih hcl.1 hfEv
        match haEv : evalSubst n unf a with
        | .outOfFuel => rw [hfEv, haEv] at h; cases h
        | .error _ => rw [hfEv, haEv] at h; cases h
        | .ok av =>
          have ⟨ha₁, ha₂⟩ := ih hcl.2 haEv
          rw [hfEv, haEv] at h
          simp only [Outcome.ok_bind] at h
          -- Cases on fv's shape, mirroring concEval_equiv.
          cases fv with
          | bvar bk =>
            -- fv is a stuck level-bvar; concEval_equiv used
            -- `concEval_not_bvar` to rule this out, but evalSubst
            -- *can* produce a level-bvar.  However, we have
            -- closedAt 0 hcl.1 → fv.closedAt 0 (via
            -- closedAt-style preservation), and a closedAt 0
            -- bvar `bk` requires `bk < 0`, which is false.
            -- Need: closedAt 0 preservation for evalSubst.
            -- WALL_closedAt_preservation_bvar.
            sorry
          | type =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | bot =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | lam dom body =>
            -- β case.  WALL_substL_depth: bridge substL → subst.
            sorry
          | iota ann body =>
            -- iota-unfold case.
            sorry
          | fix ann body =>
            -- fix-unfold case.
            sorry
          | asc t ty =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | letE vv b =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | app f' a' =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩

/-- B3-substrate-style preservation, derived from `evalSubst_equiv`. -/
theorem evalSubst_preservation_aux
    {fuel unf : Nat} {e e' τ : Expr}
    (hcl : e.closedAt 0 = true)
    (hty : Subtype' [] [] e τ)
    (hstep : evalSubst fuel unf e = .ok e') :
    Subtype' [] [] e' τ :=
  let ⟨he', _⟩ := evalSubst_equiv hcl hstep
  he'.trans hty

end Och.Soundness
