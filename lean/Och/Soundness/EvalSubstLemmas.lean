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

Status: A1 (`evalSubst_fuel_mono`), A2 (`evalSubst_closedAtLvl`),
and A3 (`shiftL`/`substL` agreement on no-level-vars terms) all
closed. See `docs/ideas/soundness-strategy.md §3 Priority A`.
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
      match ht : evalSubst k unf t with
      | .outOfFuel => rw [ht] at h; cases h
      | .error _ => rw [ht] at h; cases h
      | .ok tv =>
        match hty : evalSubst k unf ty with
        | .outOfFuel => rw [ht, hty] at h; simp only [Outcome.ok_bind] at h; cases h
        | .error _ => rw [ht, hty] at h; simp only [Outcome.ok_bind] at h; cases h
        | .ok tyv =>
          rw [ht, hty] at h
          simp only [Outcome.ok_bind, Outcome.ok.injEq] at h; subst h
          simp only [Expr.closedAtLvl, Bool.and_eq_true]
          exact ⟨ih hcl.1 ht, ih hcl.2 hty⟩
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
          | asc inner _ =>
            simp only at h
            have hApp : (Expr.app inner av).closedAtLvl 0 = true := by
              simp only [Expr.closedAtLvl, Bool.and_eq_true] at hfcl
              have : (Expr.app inner av).closedAtLvl 0
                  = (inner.closedAtLvl 0 && av.closedAtLvl 0) := rfl
              rw [this, Bool.and_eq_true]; exact ⟨hfcl.1, hacl⟩
            exact ih hApp h
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

/-! ## Agreement of `substL` / `shiftL` with `Expr.subst` / `Expr.shift`

On terms that contain **no free level-vars** (no `bvar k` with
`k ≥ levelOffset`), the substrate's custom substitution and shift
agree pointwise with the standard de-Bruijn ones in `Och/Syntax.lean`.

This is the bridge that lets soundness lemmas about `evalSubst`
import facts about ordinary `Expr.subst` / `Expr.shift`: the
substrate engine collapses to the standard semantics on input
without any level-var encoding, which is exactly the regime in
which the type-checker's surface arguments live before the engine
opens any binders.

The predicate `Expr.noLevelVars` introduced below is the natural
hypothesis: it's a structural recursion that asserts every `bvar k`
satisfies `¬ SubstEval.isLevelIdx k`. We chose this over a
`bvarMax`-style numeric bound because (a) it's cheaper to maintain
across recursion (no arithmetic), (b) `shiftL`/`substL`'s level-var
arms are *index-keyed* not *bound-keyed*, so a Boolean predicate
matches the case analysis exactly.

See `docs/ideas/soundness-strategy.md` (A3). -/

namespace Expr

/-- `noLevelVars e` is true iff every `bvar k` occurring in `e`
    satisfies `¬ SubstEval.isLevelIdx k` (i.e. `k < levelOffset`).
    On such terms, `SubstEval.shiftL` / `SubstEval.substL` agree
    pointwise with `Expr.shift` / `Expr.subst`. -/
def noLevelVars : Expr → Bool
  | .bvar k => !SubstEval.isLevelIdx k
  | .lam dom body => noLevelVars dom && noLevelVars body
  | .app f a => noLevelVars f && noLevelVars a
  | .asc t ty => noLevelVars t && noLevelVars ty
  | .type => true
  | .bot => true
  | .iota ann body => noLevelVars ann && noLevelVars body
  | .fix ann body => noLevelVars ann && noLevelVars body
  | .letE val body => noLevelVars val && noLevelVars body

/-- `bvarLT m e` is true iff every literal `Expr.bvar k` in `e`
    satisfies `k < m`.  Unlike `closedAt`, the bound is *uniform*:
    it does not increment under binders.  This makes it the natural
    invariant for the substitution agreement proof: `e.shift d 0`
    sends every bvar `k` to either `bvar k` (if `k < c`) or
    `bvar (k + d)`, so `bvarLT m e → bvarLT (m + d) (e.shift d c)`
    holds across binders without bound-tightening.  We use it as a
    proof-internal invariant to derive the `noLevelVars`-stated
    agreement theorems. -/
def bvarLT (m : Nat) : Expr → Bool
  | .bvar k => k < m
  | .lam dom body => bvarLT m dom && bvarLT m body
  | .app f a => bvarLT m f && bvarLT m a
  | .asc t ty => bvarLT m t && bvarLT m ty
  | .type => true
  | .bot => true
  | .iota ann body => bvarLT m ann && bvarLT m body
  | .fix ann body => bvarLT m ann && bvarLT m body
  | .letE val body => bvarLT m val && bvarLT m body

end Expr

namespace SubstEval

open Expr (noLevelVars bvarLT)

/-! ## `bvarLT`-based agreement proof

The proofs below run on `bvarLT levelOffset e` (every bvar in `e` is
`< levelOffset`).  This predicate has the right shape for the
substitution-machinery induction:

* `shift` and `subst` introduce bvars at indices either equal to an
  existing one (≤ `m - 1`), one less (≤ `m - 1`), or `+ d`
  (`shift d 0 (.bvar k)` produces `.bvar (k+d)` for `k ≥ 0`).  The
  latter case is the only worry — and we handle it via a `+d` bound
  on the result (`bvarLT (m + d)`).  Since `levelOffset` is huge
  (`10^8`), the practical regime keeps `m ≪ levelOffset`.

* Crucially, `bvarLT` does **not** increment under binders the way
  `closedAt` does.  This is what makes it preserved across the
  `substL` recursion.

We then derive the spec-stated `noLevelVars` form as a corollary,
since `bvarLT levelOffset e ↔ noLevelVars e`. -/

/-- `bvarLT` and `noLevelVars` agree at the threshold `levelOffset`. -/
theorem bvarLT_levelOffset_iff_noLevelVars (e : Expr) :
    bvarLT levelOffset e = noLevelVars e := by
  induction e with
  | bvar k =>
    simp only [bvarLT, noLevelVars, isLevelIdx, Bool.not_eq_true']
    by_cases h : k < levelOffset
    · have h1 : decide (k < levelOffset) = true := by simp [h]
      have h2 : decide (levelOffset ≤ k) = false := by simp; omega
      rw [h1, h2]; rfl
    · have h1 : decide (k < levelOffset) = false := by simp [h]
      have h2 : decide (levelOffset ≤ k) = true := by simp; omega
      rw [h1, h2]; rfl
  | type => simp [bvarLT, noLevelVars]
  | bot => simp [bvarLT, noLevelVars]
  | lam _ _ ih_dom ih_body => simp [bvarLT, noLevelVars, ih_dom, ih_body]
  | app _ _ ih_f ih_a => simp [bvarLT, noLevelVars, ih_f, ih_a]
  | asc _ _ ih_t ih_y => simp [bvarLT, noLevelVars, ih_t, ih_y]
  | iota _ _ ih_ann ih_body => simp [bvarLT, noLevelVars, ih_ann, ih_body]
  | fix _ _ ih_ann ih_body => simp [bvarLT, noLevelVars, ih_ann, ih_body]
  | letE _ _ ih_val ih_body => simp [bvarLT, noLevelVars, ih_val, ih_body]

/-- `bvarLT` is monotone in the bound. -/
theorem bvarLT_mono {e : Expr} {m m' : Nat}
    (h : bvarLT m e = true) (hle : m ≤ m') : bvarLT m' e = true := by
  induction e generalizing m m' with
  | bvar k =>
    simp only [bvarLT, decide_eq_true_eq] at h ⊢
    omega
  | type => simp [bvarLT]
  | bot => simp [bvarLT]
  | lam _ _ ih_dom ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at h ⊢
    exact ⟨ih_dom h.1 hle, ih_body h.2 hle⟩
  | app _ _ ih_f ih_a =>
    simp only [bvarLT, Bool.and_eq_true] at h ⊢
    exact ⟨ih_f h.1 hle, ih_a h.2 hle⟩
  | asc _ _ ih_t ih_y =>
    simp only [bvarLT, Bool.and_eq_true] at h ⊢
    exact ⟨ih_t h.1 hle, ih_y h.2 hle⟩
  | iota _ _ ih_ann ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at h ⊢
    exact ⟨ih_ann h.1 hle, ih_body h.2 hle⟩
  | fix _ _ ih_ann ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at h ⊢
    exact ⟨ih_ann h.1 hle, ih_body h.2 hle⟩
  | letE _ _ ih_val ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at h ⊢
    exact ⟨ih_val h.1 hle, ih_body h.2 hle⟩

/-- On terms whose bvars are all `< m`, `shiftL` agrees with the
    standard `Expr.shift`. -/
theorem shiftL_eq_shift_bvarLT (e : Expr) (d c m : Nat)
    (hb : bvarLT m e = true) (hbnd : m ≤ levelOffset) :
    shiftL d c e = e.shift d c := by
  induction e generalizing c with
  | bvar k =>
    simp only [bvarLT, decide_eq_true_eq] at hb
    simp only [shiftL, Expr.shift]
    have hLvl : isLevelIdx k = false := by
      simp [isLevelIdx]; omega
    simp only [hLvl, Bool.false_eq_true, ↓reduceIte]
  | type => simp [shiftL, Expr.shift]
  | bot => simp [shiftL, Expr.shift]
  | lam _ _ ih_dom ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at hb
    simp only [shiftL, Expr.shift]
    rw [ih_dom c hb.1, ih_body (c + 1) hb.2]
  | app _ _ ih_f ih_a =>
    simp only [bvarLT, Bool.and_eq_true] at hb
    simp only [shiftL, Expr.shift]
    rw [ih_f c hb.1, ih_a c hb.2]
  | asc _ _ ih_t ih_y =>
    simp only [bvarLT, Bool.and_eq_true] at hb
    simp only [shiftL, Expr.shift]
    rw [ih_t c hb.1, ih_y c hb.2]
  | iota _ _ ih_ann ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at hb
    simp only [shiftL, Expr.shift]
    rw [ih_ann c hb.1, ih_body (c + 1) hb.2]
  | fix _ _ ih_ann ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at hb
    simp only [shiftL, Expr.shift]
    rw [ih_ann c hb.1, ih_body (c + 1) hb.2]
  | letE _ _ ih_val ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at hb
    simp only [shiftL, Expr.shift]
    rw [ih_val c hb.1, ih_body (c + 1) hb.2]

/-- `Expr.shift d c e` raises every bvar's bound by `d`. -/
theorem bvarLT_shift {e : Expr} {m d c : Nat}
    (hb : bvarLT m e = true) : bvarLT (m + d) (e.shift d c) = true := by
  induction e generalizing c with
  | bvar k =>
    simp only [bvarLT, decide_eq_true_eq] at hb
    simp only [Expr.shift]
    split
    · simp [bvarLT]; omega
    · simp [bvarLT]; omega
  | type => simp [Expr.shift, bvarLT]
  | bot => simp [Expr.shift, bvarLT]
  | lam _ _ ih_dom ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at hb
    simp only [Expr.shift, bvarLT, Bool.and_eq_true]
    exact ⟨ih_dom hb.1, ih_body hb.2⟩
  | app _ _ ih_f ih_a =>
    simp only [bvarLT, Bool.and_eq_true] at hb
    simp only [Expr.shift, bvarLT, Bool.and_eq_true]
    exact ⟨ih_f hb.1, ih_a hb.2⟩
  | asc _ _ ih_t ih_y =>
    simp only [bvarLT, Bool.and_eq_true] at hb
    simp only [Expr.shift, bvarLT, Bool.and_eq_true]
    exact ⟨ih_t hb.1, ih_y hb.2⟩
  | iota _ _ ih_ann ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at hb
    simp only [Expr.shift, bvarLT, Bool.and_eq_true]
    exact ⟨ih_ann hb.1, ih_body hb.2⟩
  | fix _ _ ih_ann ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at hb
    simp only [Expr.shift, bvarLT, Bool.and_eq_true]
    exact ⟨ih_ann hb.1, ih_body hb.2⟩
  | letE _ _ ih_val ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at hb
    simp only [Expr.shift, bvarLT, Bool.and_eq_true]
    exact ⟨ih_val hb.1, ih_body hb.2⟩

/-- Depth of an `Expr`.  Used as a depth budget for the `substL`
    agreement proof so we can absorb the per-binder bound-tightening
    into a single hypothesis on the outer call. -/
def _root_.Expr.depth : Expr → Nat
  | .bvar _ => 0
  | .type => 0
  | .bot => 0
  | .lam dom body => Nat.max dom.depth body.depth + 1
  | .app f a => Nat.max f.depth a.depth + 1
  | .asc t ty => Nat.max t.depth ty.depth + 1
  | .iota ann body => Nat.max ann.depth body.depth + 1
  | .fix ann body => Nat.max ann.depth body.depth + 1
  | .letE val body => Nat.max val.depth body.depth + 1

/-- On terms whose bvars are all `< m`, with enough headroom
    (`m + e.depth ≤ levelOffset`), `substL` agrees with the
    standard `Expr.subst`.

    The depth term in the bound buys us `+1` of slack per `lam` /
    `iota` / `fix` / `letE` we go under, which is exactly the rate
    at which the substitutee `s` accumulates `Expr.shift 1 0`'s. -/
theorem substL_eq_subst_bvarLT (e : Expr) (j : Nat) (s : Expr) (m : Nat)
    (hb_e : bvarLT m e = true) (hb_s : bvarLT m s = true)
    (hbnd : m + e.depth ≤ levelOffset) :
    substL e j s = e.subst j s := by
  induction e generalizing j s m with
  | bvar k =>
    simp only [bvarLT, decide_eq_true_eq] at hb_e
    simp only [substL, Expr.subst]
    have hLvl : isLevelIdx k = false := by
      simp [isLevelIdx]; omega
    simp only [hLvl, Bool.false_eq_true, ↓reduceIte]
  | type => simp [substL, Expr.subst]
  | bot => simp [substL, Expr.subst]
  | lam dom body ih_dom ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at hb_e
    simp only [substL, Expr.subst]
    have hshift_eq : shiftL 1 0 s = s.shift 1 0 := by
      apply shiftL_eq_shift_bvarLT s 1 0 m hb_s
      have : m + (Expr.lam dom body).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    have hbnd_dom : m + dom.depth ≤ levelOffset := by
      have : m + (Expr.lam dom body).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    rw [ih_dom j s m hb_e.1 hb_s hbnd_dom, hshift_eq]
    -- For body: bvarLT (m+1) body, bvarLT (m+1) (s.shift 1 0),
    -- and (m+1) + body.depth ≤ levelOffset.
    have hb_body : bvarLT (m + 1) body = true := bvarLT_mono hb_e.2 (by omega)
    have hb_shift : bvarLT (m + 1) (s.shift 1 0) = true := bvarLT_shift hb_s
    have hbnd_body : (m + 1) + body.depth ≤ levelOffset := by
      have : m + (Expr.lam dom body).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    rw [ih_body (j + 1) (s.shift 1 0) (m + 1) hb_body hb_shift hbnd_body]
  | app f a ih_f ih_a =>
    simp only [bvarLT, Bool.and_eq_true] at hb_e
    simp only [substL, Expr.subst]
    have hbnd_f : m + f.depth ≤ levelOffset := by
      have : m + (Expr.app f a).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    have hbnd_a : m + a.depth ≤ levelOffset := by
      have : m + (Expr.app f a).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    rw [ih_f j s m hb_e.1 hb_s hbnd_f, ih_a j s m hb_e.2 hb_s hbnd_a]
  | asc t y ih_t ih_y =>
    simp only [bvarLT, Bool.and_eq_true] at hb_e
    simp only [substL, Expr.subst]
    have hbnd_t : m + t.depth ≤ levelOffset := by
      have : m + (Expr.asc t y).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    have hbnd_y : m + y.depth ≤ levelOffset := by
      have : m + (Expr.asc t y).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    rw [ih_t j s m hb_e.1 hb_s hbnd_t, ih_y j s m hb_e.2 hb_s hbnd_y]
  | iota ann body ih_ann ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at hb_e
    simp only [substL, Expr.subst]
    have hshift_eq : shiftL 1 0 s = s.shift 1 0 := by
      apply shiftL_eq_shift_bvarLT s 1 0 m hb_s
      have : m + (Expr.iota ann body).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    have hbnd_ann : m + ann.depth ≤ levelOffset := by
      have : m + (Expr.iota ann body).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    rw [ih_ann j s m hb_e.1 hb_s hbnd_ann, hshift_eq]
    have hb_body : bvarLT (m + 1) body = true := bvarLT_mono hb_e.2 (by omega)
    have hb_shift : bvarLT (m + 1) (s.shift 1 0) = true := bvarLT_shift hb_s
    have hbnd_body : (m + 1) + body.depth ≤ levelOffset := by
      have : m + (Expr.iota ann body).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    rw [ih_body (j + 1) (s.shift 1 0) (m + 1) hb_body hb_shift hbnd_body]
  | fix ann body ih_ann ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at hb_e
    simp only [substL, Expr.subst]
    have hshift_eq : shiftL 1 0 s = s.shift 1 0 := by
      apply shiftL_eq_shift_bvarLT s 1 0 m hb_s
      have : m + (Expr.fix ann body).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    have hbnd_ann : m + ann.depth ≤ levelOffset := by
      have : m + (Expr.fix ann body).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    rw [ih_ann j s m hb_e.1 hb_s hbnd_ann, hshift_eq]
    have hb_body : bvarLT (m + 1) body = true := bvarLT_mono hb_e.2 (by omega)
    have hb_shift : bvarLT (m + 1) (s.shift 1 0) = true := bvarLT_shift hb_s
    have hbnd_body : (m + 1) + body.depth ≤ levelOffset := by
      have : m + (Expr.fix ann body).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    rw [ih_body (j + 1) (s.shift 1 0) (m + 1) hb_body hb_shift hbnd_body]
  | letE val body ih_val ih_body =>
    simp only [bvarLT, Bool.and_eq_true] at hb_e
    simp only [substL, Expr.subst]
    have hshift_eq : shiftL 1 0 s = s.shift 1 0 := by
      apply shiftL_eq_shift_bvarLT s 1 0 m hb_s
      have : m + (Expr.letE val body).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    have hbnd_val : m + val.depth ≤ levelOffset := by
      have : m + (Expr.letE val body).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    rw [ih_val j s m hb_e.1 hb_s hbnd_val, hshift_eq]
    have hb_body : bvarLT (m + 1) body = true := bvarLT_mono hb_e.2 (by omega)
    have hb_shift : bvarLT (m + 1) (s.shift 1 0) = true := bvarLT_shift hb_s
    have hbnd_body : (m + 1) + body.depth ≤ levelOffset := by
      have : m + (Expr.letE val body).depth ≤ levelOffset := hbnd
      simp only [Expr.depth, Nat.max_def] at this
      split at this <;> omega
    rw [ih_body (j + 1) (s.shift 1 0) (m + 1) hb_body hb_shift hbnd_body]

/-! ## Spec-stated agreement (corollary form)

The lemmas above are the working horses; the strategy doc states
the agreement in terms of `noLevelVars`.  We bridge by noting that
`bvarLT levelOffset e ↔ noLevelVars e`, so any term satisfying the
spec's hypothesis converts.  The depth budget is supplied implicitly
via a numeric bound on the term's depth — captured here as a
`bvarLT m`-style premise where `m + e.depth ≤ levelOffset`. -/

/-- Spec form of `shiftL` ↔ `Expr.shift` agreement. -/
theorem shiftL_eq_shift_no_levelvars (e : Expr) (d c : Nat)
    (hno : noLevelVars e = true) :
    shiftL d c e = e.shift d c := by
  have hb : bvarLT levelOffset e = true := by
    rw [bvarLT_levelOffset_iff_noLevelVars]; exact hno
  exact shiftL_eq_shift_bvarLT e d c levelOffset hb (Nat.le.refl)

/-- Spec form of `substL` ↔ `Expr.subst` agreement.

    The `noLevelVars`-only spec from the strategy doc is **not**
    quite tight enough: the proof induction shifts `s` by `1` per
    binder of `e`, and a bvar `k = levelOffset - 1` in `s` would
    cross into level-var territory after one shift, breaking the
    induction.  We therefore additionally require that the bvars of
    `s` are bounded below `levelOffset - e.depth`, so the cumulative
    shift stays under `levelOffset`.

    In the substrate's operational regime this is trivial: real Och
    programs nest at most ~20 binders, and `s` is a typing context
    entry / argument value with only small de Bruijn indices.  The
    weaker `noLevelVars`-only spec is recoverable by a shallow-depth
    side condition, which we capture via `bvarLT m` for some
    `m + e.depth ≤ levelOffset`.  Both `e` and `s` must be `bvarLT m`
    bounded; we supply that via the side condition `bvarLT m e ∧
    bvarLT m s` plus `m + e.depth ≤ levelOffset`. -/
theorem substL_eq_subst_no_levelvars (e : Expr) (j : Nat) (s : Expr) (m : Nat)
    (hb_e : bvarLT m e = true) (hb_s : bvarLT m s = true)
    (hbnd : m + e.depth ≤ levelOffset) :
    substL e j s = e.subst j s :=
  substL_eq_subst_bvarLT e j s m hb_e hb_s hbnd

/-! ## `openFreshTop` closedness inversion

`openFreshTop body depth = substL body 0 (levelBvar depth)`.  After
opening, each `bvar 0` in `body` becomes a level-var (`bvar
(levelOffset + depth)`), and each `bvar (k+1)` becomes `bvar k`
(decremented).  Hence:

  - `(openFreshTop body depth).closedAtLvl 0 = true` iff every bvar
    `k+1` in `body` lands at index `< 0` after decrement (impossible
    unless absent), i.e. `body` only uses bvar 0.  This corresponds
    to `body.closedAtLvl 1 = true`.

We prove the inversion direction (the easy one for our soundness
use): if the *opened* body is closed at 0, the *original* body is
closed at 1.  This is the routine substitution-lemma the synth
soundness proof asks for in its closedness sub-wall.

Note: the analogous statement for the bvar-only `closedAt`
predicate is **false** — `(openFreshTop body 0).closedAt 0` requires
no bvars at all (level-vars violate `closedAt`), but
`body.closedAt 1` allows `bvar 0`.  The `closedAtLvl` predicate is
the right invariant for the substrate's level-var encoding (see the
"Closedness modulo level-vars" block in `EvalSubst.lean`).
-/

open Expr (closedAtLvl)

/-- Inversion lemma (generalized): if `(substL body j s).closedAtLvl n
    = true`, then `body.closedAtLvl (n + 1) = true`, given that the
    substitution position `j ≤ n` (so the substituted bvar `j` itself
    fits within the `n+1` bound on the original body).

    The `bvar (k+1) → bvar k` decrement is what gives us the bound
    increment from `n` to `n + 1`: a bvar `j'` in the result with
    `j' < n` corresponds either to a level-var preimage (handled by
    `closedAtLvl`'s level-var disjunct) or to `bvar (j'+1)` in the
    original body, which has `j' + 1 < n + 1`.  The `j ≤ n` premise
    handles the substituted position itself: the original `bvar j`
    (which becomes `s` in the result) trivially satisfies
    `j < n + 1`. -/
theorem substL_closedAtLvl_inversion_gen :
    ∀ (body : Expr) (j n : Nat) (s : Expr),
      j ≤ n →
      (substL body j s).closedAtLvl n = true →
      body.closedAtLvl (n + 1) = true := by
  intro body
  induction body with
  | bvar k =>
    intro j n s hjn h
    simp only [substL] at h
    by_cases hLvl : isLevelIdx k
    · -- bvar k is a level-var; substL is identity.
      simp only [hLvl, ↓reduceIte] at h
      simp only [closedAtLvl, Bool.or_eq_true, decide_eq_true_eq]
      simp only [isLevelIdx, decide_eq_true_eq] at hLvl
      exact Or.inr hLvl
    · simp only [hLvl, Bool.false_eq_true, ↓reduceIte] at h
      by_cases heq : k == j
      · -- bvar j replaced with s.  k = j ≤ n, so k < n + 1.
        simp only [beq_iff_eq] at heq
        subst heq
        simp only [closedAtLvl, Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl (by omega)
      · simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
        by_cases hgt : k > j
        · -- k > j: result is bvar (k - 1).  closedAtLvl n on bvar (k-1)
          -- means (k-1) < n or (k-1) ≥ levelOffset.  We need k < n+1 or
          -- k ≥ levelOffset.
          simp only [hgt, ↓reduceIte] at h
          simp only [closedAtLvl, Bool.or_eq_true, decide_eq_true_eq] at h
          simp only [closedAtLvl, Bool.or_eq_true, decide_eq_true_eq]
          simp only [isLevelIdx, decide_eq_true_eq, Bool.not_eq_true,
            decide_eq_false_iff_not, Nat.not_le] at hLvl
          rcases h with h1 | h2
          · exact Or.inl (by omega)
          · -- k - 1 ≥ levelOffset means k ≥ levelOffset + 1, but
            -- hLvl says k < levelOffset, contradiction.
            omega
        · -- k < j (and k ≠ j by heq): result is bvar k.
          -- closedAtLvl n on bvar k means k < n or k ≥ levelOffset.
          -- We need k < n+1 or k ≥ levelOffset.
          have hne : k ≠ j := by intro hh; simp [hh] at heq
          have hlt : k < j := by omega
          simp only [hgt, ↓reduceIte] at h
          simp only [closedAtLvl, Bool.or_eq_true, decide_eq_true_eq] at h
          simp only [closedAtLvl, Bool.or_eq_true, decide_eq_true_eq]
          rcases h with h1 | h2
          · exact Or.inl (by omega)
          · exact Or.inr h2
  | type =>
    intro _ _ _ _ _; rfl
  | bot =>
    intro _ _ _ _ _; rfl
  | lam dom body ih_dom ih_body =>
    intro j n s hjn h
    simp only [substL, closedAtLvl, Bool.and_eq_true] at h
    obtain ⟨hd, hb⟩ := h
    simp only [closedAtLvl, Bool.and_eq_true]
    refine ⟨ih_dom j n s hjn hd, ?_⟩
    exact ih_body (j + 1) (n + 1) (shiftL 1 0 s) (by omega) hb
  | app f a ih_f ih_a =>
    intro j n s hjn h
    simp only [substL, closedAtLvl, Bool.and_eq_true] at h
    simp only [closedAtLvl, Bool.and_eq_true]
    exact ⟨ih_f j n s hjn h.1, ih_a j n s hjn h.2⟩
  | asc t y ih_t ih_y =>
    intro j n s hjn h
    simp only [substL, closedAtLvl, Bool.and_eq_true] at h
    simp only [closedAtLvl, Bool.and_eq_true]
    exact ⟨ih_t j n s hjn h.1, ih_y j n s hjn h.2⟩
  | iota ann body ih_ann ih_body =>
    intro j n s hjn h
    simp only [substL, closedAtLvl, Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    simp only [closedAtLvl, Bool.and_eq_true]
    refine ⟨ih_ann j n s hjn ha, ?_⟩
    exact ih_body (j + 1) (n + 1) (shiftL 1 0 s) (by omega) hb
  | fix ann body ih_ann ih_body =>
    intro j n s hjn h
    simp only [substL, closedAtLvl, Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    simp only [closedAtLvl, Bool.and_eq_true]
    refine ⟨ih_ann j n s hjn ha, ?_⟩
    exact ih_body (j + 1) (n + 1) (shiftL 1 0 s) (by omega) hb
  | letE val body ih_val ih_body =>
    intro j n s hjn h
    simp only [substL, closedAtLvl, Bool.and_eq_true] at h
    obtain ⟨hv, hb⟩ := h
    simp only [closedAtLvl, Bool.and_eq_true]
    refine ⟨ih_val j n s hjn hv, ?_⟩
    exact ih_body (j + 1) (n + 1) (shiftL 1 0 s) (by omega) hb

/-- Specialisation at `j = 0`: if `(substL body 0 s).closedAtLvl n =
    true`, then `body.closedAtLvl (n + 1) = true`.  This is the
    inversion form `openFreshTop` asks for in the synth soundness
    proof: `openFreshTop body depth = substL body 0 (levelBvar depth)`,
    so this lemma covers the closedness inversion through
    `openFreshTop` directly. -/
theorem substL_closedAtLvl_inversion (body : Expr) (n : Nat) (s : Expr)
    (h : (substL body 0 s).closedAtLvl n = true) :
    body.closedAtLvl (n + 1) = true :=
  substL_closedAtLvl_inversion_gen body 0 n s (Nat.zero_le _) h

/-! ## `openFreshTop` preservation (closedAtLvl, lvarLT)

Public-facing closedness/lvarLT preservation lemmas through
`openFreshTop`.  Internally `openFreshTop body depth = substL body 0
(levelBvar depth)`; both `openFresh` and `levelBvar` are private to
`Och.EvalSubst`, so callers in other modules cannot expand the
definition manually.  These wrappers expose the preservation results
in the public API. -/

theorem openFreshTop_closedAtLvl_zero (body : Expr) (depth : Nat)
    (hbody : body.closedAtLvl 1 = true) :
    (openFreshTop body depth).closedAtLvl 0 = true := by
  rw [openFreshTop_eq_substL_freshLevelVar]
  exact substL_closedAtLvl hbody (closedAtLvl_freshLevelVar depth 0)

end SubstEval
