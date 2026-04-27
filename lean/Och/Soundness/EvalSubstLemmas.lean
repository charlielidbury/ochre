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

/-! ## Closedness preservation for `evalSubst`

Mirror of `concEval_closedAt` (`Och/Eval.lean`). The closedness
invariant here is `Expr.closedAtLvl`, not the vanilla `Expr.closedAt`:
the substrate uses a `levelOffset = 100_000_000` trick to encode free
level-vars as huge `bvar` indices, and `evalSubst` returns those
indices unchanged. Vanilla `closedAt 0` is therefore *not* preserved
by `evalSubst` on opened bodies. See `EvalSubst.lean`'s "Closedness
modulo level-vars" section for the predicate definition and the
`shiftL`/`substL` hygiene prerequisites this proof relies on.
-/

open Expr (closedAtLvl)

/-- `evalSubst` preserves `closedAtLvl 0`: evaluating a term that
    is closed-modulo-level-vars produces another such term. Mirrors
    `concEval_closedAt`. -/
theorem evalSubst_closedAtLvl {n unf : Nat} {e v : Expr}
    (hcl : e.closedAtLvl 0 = true)
    (h : evalSubst n unf e = .ok v) : v.closedAtLvl 0 = true := by
  induction n generalizing unf e v with
  | zero => rw [evalSubst.eq_1] at h; cases h
  | succ k ih =>
    match e with
    | .bvar j =>
      rw [evalSubst.eq_2] at h
      simp only [Expr.closedAtLvl, Bool.or_eq_true, decide_eq_true_eq] at hcl
      by_cases hLvl : isLevelIdx j
      · simp only [hLvl, ↓reduceIte, Outcome.ok.injEq] at h
        subst h
        simp only [Expr.closedAtLvl, Bool.or_eq_true, decide_eq_true_eq]
        simp only [isLevelIdx, decide_eq_true_eq] at hLvl
        exact Or.inr hLvl
      · simp only [hLvl, Bool.false_eq_true, ↓reduceIte] at h
        cases h
    | .type =>
      rw [evalSubst.eq_3] at h
      simp only [Outcome.ok.injEq] at h; subst h; rfl
    | .bot =>
      rw [evalSubst.eq_4] at h
      simp only [Outcome.ok.injEq] at h; subst h; rfl
    | .lam dom body =>
      rw [evalSubst.eq_5] at h
      simp only [Outcome.ok.injEq] at h; subst h; exact hcl
    | .iota ann body =>
      rw [evalSubst.eq_6] at h
      simp only [Outcome.ok.injEq] at h; subst h; exact hcl
    | .fix ann body =>
      rw [evalSubst.eq_7] at h
      simp only [Outcome.ok.injEq] at h; subst h; exact hcl
    | .asc t ty =>
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
      rw [evalSubst.eq_8] at h
      exact ih hcl.1 h
    | .letE val body =>
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
      rw [evalSubst.eq_9] at h
      match hv : evalSubst k unf val with
      | .outOfFuel => rw [hv] at h; cases h
      | .error _ => rw [hv] at h; cases h
      | .ok vVal =>
        have hvcl := ih hcl.1 hv
        rw [hv] at h
        simp only [Outcome.ok_bind] at h
        have hsub : (substL body 0 vVal).closedAtLvl 0 = true :=
          substL_closedAtLvl (by simpa using hcl.2) hvcl
        exact ih hsub h
    | .app f a =>
      simp only [Expr.closedAtLvl, Bool.and_eq_true] at hcl
      rw [evalSubst.eq_10] at h
      match hf : evalSubst k unf f with
      | .outOfFuel => rw [hf] at h; cases h
      | .error _ => rw [hf] at h; cases h
      | .ok fv =>
        have hfcl := ih hcl.1 hf
        match ha : evalSubst k unf a with
        | .outOfFuel => rw [hf, ha] at h; cases h
        | .error _ => rw [hf, ha] at h; cases h
        | .ok av =>
          have hacl := ih hcl.2 ha
          rw [hf, ha] at h
          simp only [Outcome.ok_bind] at h
          -- Helper: when the result is `.ok (.app fv av)`, closure follows
          -- from `closedAtLvl 0 fv` and `closedAtLvl 0 av`.
          cases fv with
          | bvar bk =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show (Expr.app (.bvar bk) av).closedAtLvl 0 = true
            simp only [Expr.closedAtLvl, Bool.and_eq_true]
            exact ⟨hfcl, hacl⟩
          | type =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show (Expr.app .type av).closedAtLvl 0 = true
            simp only [Expr.closedAtLvl, Bool.and_eq_true]
            exact ⟨by simp [Expr.closedAtLvl], hacl⟩
          | bot =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show (Expr.app .bot av).closedAtLvl 0 = true
            simp only [Expr.closedAtLvl, Bool.and_eq_true]
            exact ⟨by simp [Expr.closedAtLvl], hacl⟩
          | lam _dom body =>
            -- β: substitute and recurse.
            simp only at h
            simp only [Expr.closedAtLvl, Bool.and_eq_true] at hfcl
            have hsub : (substL body 0 av).closedAtLvl 0 = true :=
              substL_closedAtLvl (by simpa using hfcl.2) hacl
            exact ih hsub h
          | iota ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h
              subst h
              have : (Expr.app (.iota ann body) av).closedAtLvl 0
                  = ((Expr.iota ann body).closedAtLvl 0 && av.closedAtLvl 0) := rfl
              rw [this, Bool.and_eq_true]; exact ⟨hfcl, hacl⟩
            · have hself : (Expr.iota ann body).closedAtLvl 0 = true := hfcl
              simp only [Expr.closedAtLvl, Bool.and_eq_true] at hfcl
              have hbody : body.closedAtLvl 1 = true := by simpa using hfcl.2
              have hsub : (substL body 0 (.iota ann body)).closedAtLvl 0 = true :=
                substL_closedAtLvl hbody hself
              have hApp : (Expr.app (substL body 0 (.iota ann body)) av).closedAtLvl 0 = true := by
                have : (Expr.app (substL body 0 (.iota ann body)) av).closedAtLvl 0
                    = ((substL body 0 (.iota ann body)).closedAtLvl 0 && av.closedAtLvl 0) := rfl
                rw [this, Bool.and_eq_true]; exact ⟨hsub, hacl⟩
              exact ih hApp h
          | fix ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h
              subst h
              have : (Expr.app (.fix ann body) av).closedAtLvl 0
                  = ((Expr.fix ann body).closedAtLvl 0 && av.closedAtLvl 0) := rfl
              rw [this, Bool.and_eq_true]; exact ⟨hfcl, hacl⟩
            · have hself : (Expr.fix ann body).closedAtLvl 0 = true := hfcl
              simp only [Expr.closedAtLvl, Bool.and_eq_true] at hfcl
              have hbody : body.closedAtLvl 1 = true := by simpa using hfcl.2
              have hsub : (substL body 0 (.fix ann body)).closedAtLvl 0 = true :=
                substL_closedAtLvl hbody hself
              have hApp : (Expr.app (substL body 0 (.fix ann body)) av).closedAtLvl 0 = true := by
                have : (Expr.app (substL body 0 (.fix ann body)) av).closedAtLvl 0
                    = ((substL body 0 (.fix ann body)).closedAtLvl 0 && av.closedAtLvl 0) := rfl
                rw [this, Bool.and_eq_true]; exact ⟨hsub, hacl⟩
              exact ih hApp h
          | asc t ty =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            have : (Expr.app (.asc t ty) av).closedAtLvl 0
                = ((Expr.asc t ty).closedAtLvl 0 && av.closedAtLvl 0) := rfl
            rw [this, Bool.and_eq_true]; exact ⟨hfcl, hacl⟩
          | letE vv b =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            have : (Expr.app (.letE vv b) av).closedAtLvl 0
                = ((Expr.letE vv b).closedAtLvl 0 && av.closedAtLvl 0) := rfl
            rw [this, Bool.and_eq_true]; exact ⟨hfcl, hacl⟩
          | app f' a' =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            have : (Expr.app (.app f' a') av).closedAtLvl 0
                = ((Expr.app f' a').closedAtLvl 0 && av.closedAtLvl 0) := rfl
            rw [this, Bool.and_eq_true]; exact ⟨hfcl, hacl⟩

end SubstEval
