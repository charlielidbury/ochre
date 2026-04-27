import Och.EvalSubst

/-!
# Substrate lemmas for `evalSubst`

This module collects the structural properties of `SubstEval.evalSubst`
that the soundness proof needs.  It is the substitution-engine analogue
of the `concEval_fuel_mono` / `concEval_closedAt` block in `Och/Eval.lean`.

Scope: only the most local "engine hygiene" lemmas live here — no
appeal to `Subtype'`, no appeal to `concEval`.  Subsequent agents add
the cross-engine (e.g. `evalSubst_concEval_agree`) and substitution-
arithmetic (e.g. `substL_eq_subst_no_levelvars`) lemmas as separate
modules.

Status: A1 (`evalSubst_fuel_mono`) closed.  See
`docs/ideas/soundness-strategy.md §3 Priority A`.
-/

namespace SubstEval

open Outcome

/-! ## Fuel monotonicity for `evalSubst`

Mirror of `concEval_fuel_mono` (`Och/Eval.lean`).  The proof structure
is arm-for-arm identical; the only differences are:

* `evalSubst` is `def` (not `partial def`) — and crucially, Lean
  generates per-arm equation lemmas `evalSubst.eq_1` … `evalSubst.eq_10`
  that give us syntactic control over each step.  We rewrite with them
  directly rather than fighting `unfold` / `simp [evalSubst]` (the
  latter recurses; the former leaves un-reduced inner matches).
* `evalSubst` uses `do`-notation in `letE` / `app`, which is
  `Outcome.bind`.
* `evalSubst` has more "value" arms: `.bvar k` for level-vars,
  `.bot`.  And the neutral-app cases return `.ok (.app f' a')`
  instead of erroring.
* `evalSubst` carries an extra `unf` budget that we generalise over
  in the induction (the iota/fix unfold arms drop it by 1).

The `unf` parameter is held constant by the induction and threaded
through each recursive call.  No separate `unf` monotonicity is
proved here; if a downstream proof needs it, it should be a
companion lemma.
-/

/-- If `evalSubst n unf e` succeeds, then so does `evalSubst (n+1) unf e`
with the same value.  Mirrors `concEval_fuel_mono`. -/
theorem evalSubst_fuel_mono {n unf : Nat} {e v : Expr}
    (h : evalSubst n unf e = .ok v) : evalSubst (n + 1) unf e = .ok v := by
  induction n generalizing unf e v with
  | zero => rw [evalSubst.eq_1] at h; cases h
  | succ k ih =>
    match e with
    | .bvar k' =>
      rw [evalSubst.eq_2] at h ⊢; exact h
    | .lam _ _ =>
      rw [evalSubst.eq_5] at h ⊢; exact h
    | .type =>
      rw [evalSubst.eq_3] at h ⊢; exact h
    | .bot =>
      rw [evalSubst.eq_4] at h ⊢; exact h
    | .iota _ _ =>
      rw [evalSubst.eq_6] at h ⊢; exact h
    | .fix _ _ =>
      rw [evalSubst.eq_7] at h ⊢; exact h
    | .asc t _ =>
      rw [evalSubst.eq_8] at h ⊢
      exact ih h
    | .letE val body =>
      rw [evalSubst.eq_9] at h ⊢
      -- `do let v ← X; Y v` reduces by cases on `X`.
      match hv : evalSubst k unf val with
      | .outOfFuel => rw [hv] at h; cases h
      | .error _ => rw [hv] at h; cases h
      | .ok vVal =>
        have hv' := ih hv
        rw [hv] at h
        rw [hv']
        exact ih h
    | .app f a =>
      rw [evalSubst.eq_10] at h ⊢
      match hf : evalSubst k unf f with
      | .outOfFuel => rw [hf] at h; cases h
      | .error _ => rw [hf] at h; cases h
      | .ok fv =>
        have hf' := ih hf
        match ha : evalSubst k unf a with
        | .outOfFuel => rw [hf, ha] at h; cases h
        | .error _ => rw [hf, ha] at h; cases h
        | .ok av =>
          have ha' := ih ha
          rw [hf, ha] at h
          rw [hf', ha']
          -- Discharge the binds (`do let _ ← ok _; ...` collapses).
          simp only [Outcome.ok_bind] at h ⊢
          -- After the binds, both sides have `match fv with ...`.
          -- Cases on `fv`'s shape, then reduce the match via `simp only`
          -- (the literal pattern triggers reduction).
          cases fv with
          | bvar _ => simp only at h ⊢; exact h
          | type => simp only at h ⊢; exact h
          | bot => simp only at h ⊢; exact h
          | lam _dom body =>
            -- β: substitute and recurse.
            simp only at h ⊢
            exact ih h
          | iota _ann body =>
            simp only at h ⊢
            -- `if isNeutral av || unf == 0 then ok else recurse`.
            split at h
            · rename_i hcond; rw [if_pos hcond]; exact h
            · rename_i hcond; rw [if_neg hcond]; exact ih h
          | fix _ann body =>
            simp only at h ⊢
            split at h
            · rename_i hcond; rw [if_pos hcond]; exact h
            · rename_i hcond; rw [if_neg hcond]; exact ih h
          | asc _ _ => simp only at h ⊢; exact h
          | letE _ _ => simp only at h ⊢; exact h
          | app _ _ => simp only at h ⊢; exact h

end SubstEval
