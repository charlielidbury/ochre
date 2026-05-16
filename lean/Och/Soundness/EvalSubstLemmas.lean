import Och.EvalSubst

/-!
# Substrate lemmas for `evalSubst`

This module collects the structural properties of `SubstEval.evalSubst`
that the soundness proof needs.

## Status (post de Bruijn refactor)

- A1 (`evalSubst_fuel_mono`) — closed.
- A2 (`evalSubst_closedAt`) — sorry'd, needs re-proof for standard
  `closedAt` (old proof used removed `closedAtLvl`/`substL`).
- A3 (`subst_closedAt`) — sorry'd, straightforward induction deferred.

The old `shiftL`/`substL` agreement block and `closedAtLvl`
infrastructure have been removed entirely; the pure de Bruijn
engine uses only `Expr.subst`/`Expr.shift` from `Syntax.lean`.
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
    | .asc t ty =>
      rw [evalSubst.eq_8] at h ⊢
      match ht : evalSubst k unf t with
      | .outOfFuel => rw [ht] at h; cases h
      | .error _ => rw [ht] at h; cases h
      | .ok tv =>
        have ht' := ih ht
        match hty : evalSubst k unf ty with
        | .outOfFuel => rw [ht, hty] at h; simp only [Outcome.ok_bind] at h; cases h
        | .error _ => rw [ht, hty] at h; simp only [Outcome.ok_bind] at h; cases h
        | .ok tyv =>
          have hty' := ih hty
          rw [ht, hty] at h
          rw [ht', hty']
          exact h
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
          | asc _ _ => simp only at h ⊢; exact ih h
          | letE _ _ => simp only at h ⊢; exact h
          | app _ _ => simp only at h ⊢; exact h

/-! ## Closedness preservation for `evalSubst`

In the pure de Bruijn regime, the relevant closedness property is
`Expr.closedAt n`: every free `bvar k` in the term satisfies `k < n`.
The `evalSubst` evaluator preserves `closedAt 0` on closed terms
(it only reduces redexes, never introduces free variables). The old
`closedAtLvl` / `substL` infrastructure has been removed as part of
the de Bruijn refactor; the lemmas below are sorry'd pending
re-proof in the new regime.

The downstream soundness modules still reference some of these
names; we provide sorry'd stubs so the project compiles. -/

/-- `evalSubst` preserves closedness: evaluating a closed term
    produces a closed term. (Sorry'd — needs re-proof for pure de
    Bruijn; the old proof relied on `closedAtLvl`/`substL` which no
    longer exist.) -/
theorem evalSubst_closedAt {n unf : Nat} {e v : Expr}
    (hcl : e.closedAt 0 = true)
    (h : evalSubst n unf e = .ok v) : v.closedAt 0 = true := by
  sorry

/-- `Expr.subst` preserves closedness: substituting a closed term
    into a body that's closed at depth 1 yields a closed term.
    (Sorry'd — straightforward induction, deferred.) -/
theorem subst_closedAt (body : Expr) (s : Expr)
    (hbody : body.closedAt 1 = true)
    (hs : s.closedAt 0 = true) :
    (body.subst 0 s).closedAt 0 = true := by
  sorry

end SubstEval
