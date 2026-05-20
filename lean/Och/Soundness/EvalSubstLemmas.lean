import Och.EvalSubst

/-!
# Substrate lemmas for `evalSubst`

This module collects the structural properties of `SubstEval.evalSubst`
that the soundness proof needs.

## Status (post de Bruijn refactor)

- A1 (`evalSubst_fuel_mono`) — closed.
- A2 (`evalSubst_closedAt`) — closed.
- A3 (`subst_closedAt`) — closed.

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
  generates per-arm equation lemmas `evalSubst.eq_1` … `evalSubst.eq_8`
  that give us syntactic control over each step.  We rewrite with them
  directly rather than fighting `unfold` / `simp [evalSubst]` (the
  latter recurses; the former leaves un-reduced inner matches).
* `evalSubst` uses `do`-notation in `app`, which is
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
    | .fix _ =>
      rw [evalSubst.eq_7] at h ⊢; exact h
    | .app f a =>
      rw [evalSubst.eq_8] at h ⊢
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
          | fix body =>
            simp only at h ⊢
            split at h
            · rename_i hcond; rw [if_pos hcond]; exact h
            · rename_i hcond; rw [if_neg hcond]; exact ih h
          | app _ _ => simp only at h ⊢; exact h

/-! ## Closedness preservation for `Expr.subst` and `evalSubst`

In the pure de Bruijn regime, the relevant closedness property is
`Expr.closedAt n`: every free `bvar k` in the term satisfies `k < n`.
-/

/-- Generalized `subst_closedAt`: substituting at index `j ≤ n` with
    a term closed at `n` into a body closed at `n+1` yields a term
    closed at `n`. Needed for the induction step under binders. -/
private theorem subst_closedAt_gen (body : Expr) (s : Expr) (n j : Nat)
    (hj : j ≤ n)
    (hbody : body.closedAt (n + 1) = true)
    (hs : s.closedAt n = true) :
    (body.subst j s).closedAt n = true := by
  induction body generalizing s j n with
  | bvar k =>
    unfold Expr.subst
    split
    · -- k == j: result is s
      exact hs
    · split
      · -- k > j: result is bvar (k-1)
        simp only [Expr.closedAt, decide_eq_true_eq] at hbody ⊢
        omega
      · -- k < j: result is bvar k
        rename_i hne hngt
        simp only [beq_iff_eq] at hne
        simp only [Nat.not_lt] at hngt
        simp only [Expr.closedAt, decide_eq_true_eq] at hbody ⊢
        omega
  | lam dom body ih_dom ih_body =>
    simp only [Expr.subst, Expr.closedAt, Bool.and_eq_true] at hbody ⊢
    exact ⟨ih_dom s n j hj hbody.1 hs,
           ih_body (s.shift 1 0) (n + 1) (j + 1) (by omega) hbody.2
             (Expr.shift_closedAt s n 1 0 (Nat.zero_le n) hs)⟩
  | app f a ih_f ih_a =>
    simp only [Expr.subst, Expr.closedAt, Bool.and_eq_true] at hbody ⊢
    exact ⟨ih_f s n j hj hbody.1 hs, ih_a s n j hj hbody.2 hs⟩
  | type => simp [Expr.subst, Expr.closedAt]
  | bot => simp [Expr.subst, Expr.closedAt]
  | iota ann body ih_ann ih_body =>
    simp only [Expr.subst, Expr.closedAt, Bool.and_eq_true] at hbody ⊢
    exact ⟨ih_ann s n j hj hbody.1 hs,
           ih_body (s.shift 1 0) (n + 1) (j + 1) (by omega) hbody.2
             (Expr.shift_closedAt s n 1 0 (Nat.zero_le n) hs)⟩
  | fix body ih_body =>
    simp only [Expr.subst, Expr.closedAt] at hbody ⊢
    exact ih_body (s.shift 1 0) (n + 1) (j + 1) (by omega) hbody
             (Expr.shift_closedAt s n 1 0 (Nat.zero_le n) hs)

/-- `Expr.subst` preserves closedness: substituting a closed term
    into a body that's closed at depth 1 yields a closed term. -/
theorem subst_closedAt (body : Expr) (s : Expr)
    (hbody : body.closedAt 1 = true)
    (hs : s.closedAt 0 = true) :
    (body.subst 0 s).closedAt 0 = true :=
  subst_closedAt_gen body s 0 0 (Nat.le_refl 0) hbody hs

/-- `evalSubst` preserves closedness: evaluating a closed term
    produces a closed term. -/
theorem evalSubst_closedAt {n unf : Nat} {e v : Expr}
    (hcl : e.closedAt 0 = true)
    (h : evalSubst n unf e = .ok v) : v.closedAt 0 = true := by
  induction n generalizing unf e v with
  | zero => rw [evalSubst.eq_1] at h; cases h
  | succ k ih =>
    match e with
    | .bvar k' =>
      rw [evalSubst.eq_2] at h; cases h; exact hcl
    | .type =>
      rw [evalSubst.eq_3] at h; cases h; simp [Expr.closedAt]
    | .bot =>
      rw [evalSubst.eq_4] at h; cases h; simp [Expr.closedAt]
    | .lam _ _ =>
      rw [evalSubst.eq_5] at h; cases h; exact hcl
    | .iota _ _ =>
      rw [evalSubst.eq_6] at h; cases h; exact hcl
    | .fix _ =>
      rw [evalSubst.eq_7] at h; cases h; exact hcl
    | .app f a =>
      rw [evalSubst.eq_8] at h
      simp only [Expr.closedAt, Bool.and_eq_true] at hcl
      match hf : evalSubst k unf f with
      | .outOfFuel => rw [hf] at h; cases h
      | .error _ => rw [hf] at h; cases h
      | .ok fv =>
        match ha : evalSubst k unf a with
        | .outOfFuel => rw [hf, ha] at h; cases h
        | .error _ => rw [hf, ha] at h; cases h
        | .ok av =>
          rw [hf, ha] at h
          simp only [Outcome.ok_bind] at h
          have hfCl := ih hcl.1 hf
          have haCl := ih hcl.2 ha
          cases fv with
          | bvar _ =>
            simp only at h; cases h
            simp only [Expr.closedAt, Bool.and_eq_true]
            exact ⟨hfCl, haCl⟩
          | type =>
            simp only at h; cases h
            simp only [Expr.closedAt, Bool.and_eq_true]
            exact ⟨by simp [Expr.closedAt], haCl⟩
          | bot =>
            simp only at h; cases h
            simp only [Expr.closedAt, Bool.and_eq_true]
            exact ⟨by simp [Expr.closedAt], haCl⟩
          | lam _dom body =>
            simp only at h
            simp only [Expr.closedAt, Bool.and_eq_true] at hfCl
            exact ih (subst_closedAt body av hfCl.2 haCl) h
          | iota _ann body =>
            simp only at h
            split at h
            · cases h
              simp only [Expr.closedAt, Bool.and_eq_true] at hfCl ⊢
              exact ⟨⟨hfCl.1, hfCl.2⟩, haCl⟩
            · simp only [Expr.closedAt, Bool.and_eq_true] at hfCl
              have hsubCl := subst_closedAt body (.iota _ann body) hfCl.2
                (by simp [Expr.closedAt, Bool.and_eq_true]; exact hfCl)
              have happCl : (Expr.app (body.subst 0 (.iota _ann body)) av).closedAt 0 = true := by
                simp only [Expr.closedAt, Bool.and_eq_true]; exact ⟨hsubCl, haCl⟩
              exact ih happCl h
          | fix body =>
            simp only at h
            split at h
            · cases h
              simp only [Expr.closedAt, Bool.and_eq_true] at hfCl ⊢
              exact ⟨hfCl, haCl⟩
            · simp only [Expr.closedAt] at hfCl
              have hsubCl := subst_closedAt body (.fix body) hfCl
                (by simp [Expr.closedAt]; exact hfCl)
              have happCl : (Expr.app (body.subst 0 (.fix body)) av).closedAt 0 = true := by
                simp only [Expr.closedAt, Bool.and_eq_true]; exact ⟨hsubCl, haCl⟩
              exact ih happCl h
          | app _ _ =>
            simp only at h; cases h
            simp only [Expr.closedAt, Bool.and_eq_true] at hfCl ⊢
            exact ⟨⟨hfCl.1, hfCl.2⟩, haCl⟩

end SubstEval
