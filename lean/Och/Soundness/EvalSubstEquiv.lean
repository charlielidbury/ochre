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

/-! ## Substitution bridge sub-lemmas

These lemmas state that `substL b 0 v = Expr.subst b 0 v` on the
substrate's hygiene regime (`closedAt 0` plus a depth budget).  They
are the obligation the substrate owes the declarative system — the
core wall.  We isolate them as named lemmas so the main equivalence
proof has structure.

The core difficulty: `substL_eq_subst_bvarLT` requires a single
`bvarLT m` bound covering both the body and the substitutee, with
`m + body.depth ≤ levelOffset`.  Threading such a bound through
recursive evaluation (β reduces a term whose body+arg sub-depths
can compose unfavourably) needs a global invariant that closedAt 0
alone doesn't provide.  We surface this as a separate hypothesis
`evalSubst_substL_bridge` which the per-call site provides.

For now, the bridge sorry-stubs remain — the wall is the "depth
budget threading" subtask, not the bidirectional conversion that
would follow from it.  See `WALL_substL_depth` below. -/

/-- Bridge between `SubstEval.substL` and `Expr.subst` for the
β/iota/fix/let arms.

On `closedAt 0` inputs with a depth budget
`body.depth + s.depth + 1 ≤ SubstEval.levelOffset`, this collapses
to `SubstEval.substL_eq_subst_bvarLT` after a `bvarLT` bound
derivation.  In practice the budget is trivial (programs nest at
most ~100 binders; `levelOffset = 10^8`).

The remaining wall (`WALL_substL_depth` below) is **propagating
this depth budget through `evalSubst`'s recursion**: β-substitution
can produce a term whose depth combines body.depth and s.depth,
growing without an obvious bound.  We expose the budget-aware
helper as a separate, fully-proven lemma; the wall is the
unconditional version that drops the budget. -/
private theorem substL_eq_subst_at_zero (body s : Expr)
    (hbody_cl : closedAt 1 body = true)
    (hs_cl : closedAt 0 s = true)
    (hbnd : 2 * body.depth + s.depth + 1 ≤ levelOffset) :
    substL body 0 s = body.subst 0 s := by
  let m := Nat.max (1 + body.depth) s.depth
  have hm_body : 1 + body.depth ≤ m := Nat.le_max_left _ _
  have hm_s : s.depth ≤ m := Nat.le_max_right _ _
  have hb_body : bvarLT m body = true := by
    have := bvarLT_of_closedAt body 1 hbody_cl
    exact bvarLT_mono this hm_body
  have hb_s : bvarLT m s = true := by
    have h0 : bvarLT (0 + s.depth) s = true := bvarLT_of_closedAt s 0 hs_cl
    have h2 : bvarLT s.depth s = true := by simpa using h0
    exact bvarLT_mono h2 hm_s
  have hbnd' : m + body.depth ≤ levelOffset := by
    have hm_def : m = Nat.max (1 + body.depth) s.depth := rfl
    rw [hm_def]
    simp only [Nat.max_def]
    split <;> omega
  exact substL_eq_subst_bvarLT body 0 s m hb_body hb_s hbnd'

/-- WALL: unconditional `substL = subst` bridge.  This asserts the
depth budget `body.depth + s.depth + 1 ≤ levelOffset` unconditionally;
discharging it via `substL_eq_subst_at_zero` requires propagating
the depth budget through evalSubst's recursion (β can grow term
depth).  Left as a sorry-stub; in practice the budget always holds
for realistic programs (`levelOffset = 10^8`). -/
private theorem WALL_substL_depth (body s : Expr)
    (hbody_cl : closedAt 1 body = true)
    (hs_cl : closedAt 0 s = true) :
    substL body 0 s = body.subst 0 s :=
  substL_eq_subst_at_zero body s hbody_cl hs_cl (by
    -- WALL: depth budget assumed, no proof yet (β can grow depth).
    sorry)

/-- `evalSubst` preserves `closedAt 0`.  Uses the substL→subst
bridge to apply standard `Expr.subst_closedAt`.  Mirrors
`concEval_closedAt`. -/
theorem evalSubst_closedAt {n unf : Nat} {e v : Expr}
    (hcl : e.closedAt 0 = true)
    (h : evalSubst n unf e = .ok v) : v.closedAt 0 = true := by
  induction n generalizing unf e v with
  | zero => rw [evalSubst.eq_1] at h; cases h
  | succ k ih =>
    match e with
    | .bvar j =>
      simp only [closedAt, decide_eq_true_eq] at hcl
      omega
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
      simp only [closedAt, Bool.and_eq_true] at hcl
      rw [evalSubst.eq_8] at h
      exact ih hcl.1 h
    | .letE val body =>
      simp only [closedAt, Bool.and_eq_true] at hcl
      rw [evalSubst.eq_9] at h
      match hv : evalSubst k unf val with
      | .outOfFuel => rw [hv] at h; cases h
      | .error _ => rw [hv] at h; cases h
      | .ok vVal =>
        have hvcl := ih hcl.1 hv
        rw [hv] at h
        simp only [Outcome.ok_bind] at h
        -- substL body 0 vVal = body.subst 0 vVal via WALL.
        have heq : substL body 0 vVal = body.subst 0 vVal :=
          WALL_substL_depth body vVal (by simpa using hcl.2) hvcl
        rw [heq] at h
        have hsub : (body.subst 0 vVal).closedAt 0 = true :=
          Expr.subst_closedAt (by simpa using hcl.2) hvcl
        exact ih hsub h
    | .app f a =>
      simp only [closedAt, Bool.and_eq_true] at hcl
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
          cases fv with
          | bvar bk =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show (Expr.app (.bvar bk) av).closedAt 0 = true
            simp only [closedAt, Bool.and_eq_true]
            exact ⟨hfcl, hacl⟩
          | type =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show (Expr.app .type av).closedAt 0 = true
            simp only [closedAt, Bool.and_eq_true]
            exact ⟨by simp [closedAt], hacl⟩
          | bot =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            show (Expr.app .bot av).closedAt 0 = true
            simp only [closedAt, Bool.and_eq_true]
            exact ⟨by simp [closedAt], hacl⟩
          | lam _dom body =>
            simp only at h
            simp only [closedAt, Bool.and_eq_true] at hfcl
            have heq : substL body 0 av = body.subst 0 av :=
              WALL_substL_depth body av (by simpa using hfcl.2) hacl
            rw [heq] at h
            have hsub : (body.subst 0 av).closedAt 0 = true :=
              Expr.subst_closedAt (by simpa using hfcl.2) hacl
            exact ih hsub h
          | iota ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h
              subst h
              have hh : (Expr.app (.iota ann body) av).closedAt 0
                  = (closedAt 0 (Expr.iota ann body) && closedAt 0 av) := rfl
              rw [hh, Bool.and_eq_true]
              exact ⟨hfcl, hacl⟩
            · have hself : (Expr.iota ann body).closedAt 0 = true := hfcl
              simp only [closedAt, Bool.and_eq_true] at hfcl
              have hbody : body.closedAt 1 = true := by simpa using hfcl.2
              have heq : substL body 0 (.iota ann body) =
                  body.subst 0 (.iota ann body) :=
                WALL_substL_depth body _ hbody hself
              rw [heq] at h
              have hsub : (body.subst 0 (.iota ann body)).closedAt 0 = true :=
                Expr.subst_closedAt hbody hself
              have hApp : (Expr.app (body.subst 0 (.iota ann body)) av).closedAt 0
                  = true := by
                simp only [closedAt, Bool.and_eq_true]; exact ⟨hsub, hacl⟩
              exact ih hApp h
          | fix ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h
              subst h
              have hh : (Expr.app (.fix ann body) av).closedAt 0
                  = (closedAt 0 (Expr.fix ann body) && closedAt 0 av) := rfl
              rw [hh, Bool.and_eq_true]
              exact ⟨hfcl, hacl⟩
            · have hself : (Expr.fix ann body).closedAt 0 = true := hfcl
              simp only [closedAt, Bool.and_eq_true] at hfcl
              have hbody : body.closedAt 1 = true := by simpa using hfcl.2
              have heq : substL body 0 (.fix ann body) =
                  body.subst 0 (.fix ann body) :=
                WALL_substL_depth body _ hbody hself
              rw [heq] at h
              have hsub : (body.subst 0 (.fix ann body)).closedAt 0 = true :=
                Expr.subst_closedAt hbody hself
              have hApp : (Expr.app (body.subst 0 (.fix ann body)) av).closedAt 0
                  = true := by
                simp only [closedAt, Bool.and_eq_true]; exact ⟨hsub, hacl⟩
              exact ih hApp h
          | asc t ty =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            have hh : (Expr.app (.asc t ty) av).closedAt 0
                = (closedAt 0 (Expr.asc t ty) && closedAt 0 av) := rfl
            rw [hh, Bool.and_eq_true]
            exact ⟨hfcl, hacl⟩
          | letE vv b =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            have hh : (Expr.app (.letE vv b) av).closedAt 0
                = (closedAt 0 (Expr.letE vv b) && closedAt 0 av) := rfl
            rw [hh, Bool.and_eq_true]
            exact ⟨hfcl, hacl⟩
          | app f' a' =>
            simp only at h
            simp only [Outcome.ok.injEq] at h
            subst h
            have hh : (Expr.app (.app f' a') av).closedAt 0
                = (closedAt 0 (Expr.app f' a') && closedAt 0 av) := rfl
            rw [hh, Bool.and_eq_true]
            exact ⟨hfcl, hacl⟩

/-! ## Main equivalence (partial)

We prove the bidirectional equivalence on `closedAt 0` inputs.  The
β/iota-unfold/fix-unfold/letE arms route through `WALL_substL_depth`
above. -/

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
      simp only [closedAt, Bool.and_eq_true] at hcl
      rw [evalSubst.eq_9] at h
      match hvEv : evalSubst n unf val with
      | .outOfFuel => rw [hvEv] at h; cases h
      | .error _ => rw [hvEv] at h; cases h
      | .ok vv =>
        simp only [hvEv] at h
        have ⟨hvv₁, hvv₂⟩ := ih hcl.1 hvEv
        have hvv_cl : vv.closedAt 0 = true := evalSubst_closedAt hcl.1 hvEv
        -- substL body 0 vv = body.subst 0 vv via WALL.
        have heq : substL body 0 vv = body.subst 0 vv :=
          WALL_substL_depth body vv (by simpa using hcl.2) hvv_cl
        simp only [Outcome.ok_bind] at h
        rw [heq] at h
        have hbsub_cl : (body.subst 0 vv).closedAt 0 = true :=
          Expr.subst_closedAt (by simpa using hcl.2) hvv_cl
        have ⟨he₁, he₂⟩ := ih hbsub_cl h
        refine ⟨?_, ?_⟩
        · -- e' ⊑ letE val body
          -- e' ⊑ body.subst 0 vv ⊑ letE vv body ⊑ letE val body
          have step1 : Subtype' [] [] (body.subst 0 vv) (.letE vv body) :=
            .letE_R (.refl _)
          have step2 : Subtype' [] [] (.letE vv body) (.letE val body) :=
            .letE_cong hvv₁ (.refl _)
          exact .trans he₁ (.trans step1 step2)
        · have step1 : Subtype' [] [] (.letE val body) (.letE vv body) :=
            .letE_cong hvv₂ (.refl _)
          have step2 : Subtype' [] [] (.letE vv body) (body.subst 0 vv) :=
            .letE_L (.refl _)
          exact .trans step1 (.trans step2 he₂)
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
          have hfv_cl : fv.closedAt 0 = true := evalSubst_closedAt hcl.1 hfEv
          have hav_cl : av.closedAt 0 = true := evalSubst_closedAt hcl.2 haEv
          cases fv with
          | bvar bk =>
            -- closedAt 0 fv → bk < 0, contradiction.
            simp only [closedAt, decide_eq_true_eq] at hfv_cl
            omega
          | type =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | bot =>
            simp only at h
            simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | lam dom body =>
            -- β case.
            simp only at h
            simp only [closedAt, Bool.and_eq_true] at hfv_cl
            -- substL body 0 av = body.subst 0 av via WALL.
            have heq : substL body 0 av = body.subst 0 av :=
              WALL_substL_depth body av (by simpa using hfv_cl.2) hav_cl
            rw [heq] at h
            have hbsub_cl : (body.subst 0 av).closedAt 0 = true :=
              Expr.subst_closedAt (by simpa using hfv_cl.2) hav_cl
            have ⟨he₁, he₂⟩ := ih hbsub_cl h
            refine ⟨?_, ?_⟩
            · have step1 : Subtype' [] [] (body.subst 0 av)
                  (.app (.lam dom body) av) := .beta_R (.refl _)
              have step2 : Subtype' [] [] (.app (.lam dom body) av)
                  (.app f a) := .app_cong hf₁ ha₁ ha₂
              exact .trans he₁ (.trans step1 step2)
            · have step1 : Subtype' [] [] (.app f a)
                  (.app (.lam dom body) av) := .app_cong hf₂ ha₂ ha₁
              have step2 : Subtype' [] [] (.app (.lam dom body) av)
                  (body.subst 0 av) := .beta_L (.refl _)
              exact .trans step1 (.trans step2 he₂)
          | iota ann body =>
            -- iota-unfold case (when neither neutral nor unf=0).
            simp only at h
            split at h
            · -- Stuck: returns .ok (.app (.iota ann body) av).
              rename_i hcond
              simp only [Outcome.ok.injEq] at h; subst h
              refine ⟨?_, ?_⟩
              · exact .app_cong hf₁ ha₁ ha₂
              · exact .app_cong hf₂ ha₂ ha₁
            · -- Unfolds.  Bridge substL → subst then apply unfold_iota_L/R.
              rename_i hcond
              have hself : (Expr.iota ann body).closedAt 0 = true := hfv_cl
              simp only [closedAt, Bool.and_eq_true] at hfv_cl
              have hbody : body.closedAt 1 = true := by simpa using hfv_cl.2
              have heq : substL body 0 (.iota ann body) =
                  body.subst 0 (.iota ann body) :=
                WALL_substL_depth body _ hbody hself
              rw [heq] at h
              have hbsub_cl : (body.subst 0 (.iota ann body)).closedAt 0 = true :=
                Expr.subst_closedAt hbody hself
              have hAppCl : (Expr.app (body.subst 0 (.iota ann body)) av).closedAt 0
                  = true := by
                simp only [closedAt, Bool.and_eq_true]; exact ⟨hbsub_cl, hav_cl⟩
              have ⟨he₁, he₂⟩ := ih hAppCl h
              have hUnfoldF : Subtype' [] [] (.iota ann body)
                  (body.subst 0 (.iota ann body)) :=
                .unfold_iota_L (.refl _)
              have hUnfoldB : Subtype' [] [] (body.subst 0 (.iota ann body))
                  (.iota ann body) :=
                .unfold_iota_R (.refl _)
              refine ⟨?_, ?_⟩
              · have step1 : Subtype' [] [] (.app (body.subst 0 (.iota ann body)) av)
                    (.app (.iota ann body) av) :=
                  .app_cong hUnfoldB (.refl _) (.refl _)
                have step2 : Subtype' [] [] (.app (.iota ann body) av)
                    (.app f a) := .app_cong hf₁ ha₁ ha₂
                exact .trans he₁ (.trans step1 step2)
              · have step1 : Subtype' [] [] (.app f a)
                    (.app (.iota ann body) av) := .app_cong hf₂ ha₂ ha₁
                have step2 : Subtype' [] [] (.app (.iota ann body) av)
                    (.app (body.subst 0 (.iota ann body)) av) :=
                  .app_cong hUnfoldF (.refl _) (.refl _)
                exact .trans step1 (.trans step2 he₂)
          | fix ann body =>
            -- fix-unfold case (mirror of iota).
            simp only at h
            split at h
            · rename_i hcond
              simp only [Outcome.ok.injEq] at h; subst h
              refine ⟨?_, ?_⟩
              · exact .app_cong hf₁ ha₁ ha₂
              · exact .app_cong hf₂ ha₂ ha₁
            · rename_i hcond
              have hself : (Expr.fix ann body).closedAt 0 = true := hfv_cl
              simp only [closedAt, Bool.and_eq_true] at hfv_cl
              have hbody : body.closedAt 1 = true := by simpa using hfv_cl.2
              have heq : substL body 0 (.fix ann body) =
                  body.subst 0 (.fix ann body) :=
                WALL_substL_depth body _ hbody hself
              rw [heq] at h
              have hbsub_cl : (body.subst 0 (.fix ann body)).closedAt 0 = true :=
                Expr.subst_closedAt hbody hself
              have hAppCl : (Expr.app (body.subst 0 (.fix ann body)) av).closedAt 0
                  = true := by
                simp only [closedAt, Bool.and_eq_true]; exact ⟨hbsub_cl, hav_cl⟩
              have ⟨he₁, he₂⟩ := ih hAppCl h
              have hUnfoldF : Subtype' [] [] (.fix ann body)
                  (body.subst 0 (.fix ann body)) :=
                .unfold_fix_L (.refl _)
              have hUnfoldB : Subtype' [] [] (body.subst 0 (.fix ann body))
                  (.fix ann body) :=
                .unfold_fix_R (.refl _)
              refine ⟨?_, ?_⟩
              · have step1 : Subtype' [] [] (.app (body.subst 0 (.fix ann body)) av)
                    (.app (.fix ann body) av) :=
                  .app_cong hUnfoldB (.refl _) (.refl _)
                have step2 : Subtype' [] [] (.app (.fix ann body) av)
                    (.app f a) := .app_cong hf₁ ha₁ ha₂
                exact .trans he₁ (.trans step1 step2)
              · have step1 : Subtype' [] [] (.app f a)
                    (.app (.fix ann body) av) := .app_cong hf₂ ha₂ ha₁
                have step2 : Subtype' [] [] (.app (.fix ann body) av)
                    (.app (body.subst 0 (.fix ann body)) av) :=
                  .app_cong hUnfoldF (.refl _) (.refl _)
                exact .trans step1 (.trans step2 he₂)
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
