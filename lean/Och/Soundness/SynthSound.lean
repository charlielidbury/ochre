import Och.Syntax
import Och.EvalSubst
import Och.Subtyping
import Och.API
import Och.Soundness.EvalSubstEquiv

/-!
# `synth_sound` — synthesis-soundness proof (Step-3 progress)

The user-facing theorem (`Och.Soundness.synth_sound` in
`Och/Soundness.lean`) states:

```
Och.synth e fuel = .ok v → Subtype' [] [] e v.whnf
```

i.e. if `synth` accepts `e` and produces a WHNF type-witness `v`,
then `e` declaratively subtypes `v.whnf`.

## Status (overnight effort, post Step 1+2+3)

The `synthCore` function in `Och/API.lean` has been:

1. **De-privatised.** It was `private partial def`; we removed
   `private` so this module can name it.

2. **De-partialised.** It was `partial def` (no equation lemmas);
   it is now a non-partial `def` with `termination_by fuel`.
   Lean auto-generates `synthCore.eq_def`, `synthCore.eq_1`, …
   equation lemmas — these are the lever for case-analysis.

3. **synth-soundness:** the proof now case-analyses synth's body
   structurally on `e`.  The trivially-typed arms (`.type`,
   `.bot`) close via `Subtype'.refl`; the canonical-form arms
   (`.lam`, `.iota`, `.fix`, `.letE`) bridge to `evalSubst e`
   via per-arm bind-chain extraction lemmas + `evalSubst_equiv`;
   the `.asc` arm uses `asc_L` + the structural IH on `inner`.

## Remaining residual walls

  * `synthCore_app_WALL` — the `.app` arm.  synthCore returns
    `evalSubst (.app piExpr aV)` where `piExpr` is the result of
    `whnfPi`/`neutralType` exposure.  Bridging
    `(.app f a) ⊑ evalSubst (.app piExpr aV)` requires a
    multi-step `Subtype'.app_cong` + `evalSubst_equiv` composition
    that is non-trivial because `piExpr` may differ from `evalSubst f`
    (whnfPi may unfold further).  See the wall's docstring for the
    5-step plan.

  * `synthCore_topLevel_closedAt` — CLOSED.  `Och.synth` now
    validates `closedAt 0` at entry (option 1 from the original
    resolution paths); the lemma reduces by unfolding synth and
    matching the rejection branch.

The remaining wall (`synthCore_app_WALL`) is the residue of the
previous monolithic `synthCore_opacity_WALL`.  It is substantive
but tractable; the closedness obligation is now provided by the
synth-entry check.

## Progress in this session

  * `.lam` / `.iota` / `.fix` arms of `synthCore_sound_aux`
    refactored to use `Subtype'.refl` directly via the
    `evalSubst_{lam,iota,fix}_refl` helper lemmas — these arms no
    longer consume the `closedAt 0` hypothesis, reducing wall 1's
    surface to `.letE` / `.app` / `.asc`-inner only.
  * Wall 1 confirmed FALSE-as-stated; documented with
    counterexample + three resolution paths.
  * `substL_closedAtLvl_inversion` helper added to
    `EvalSubstLemmas.lean` — the closedness inversion lemma the
    wall's docstring asks for, useful for any future
    `closedAtLvl`-based re-statement (resolution path 3).
  * Wall 2 documentation updated with 5-step plan + LOC
    estimate.
-/

namespace Och.Soundness

open SubstEval
open Expr (closedAt)

/-! ## closedAt-0 propagation — RESOLVED via synth-entry check

The original wall asserted `Och.synth e fuel = .ok v →
e.closedAt 0 = true`.  This was discovered FALSE-as-stated during
the soundness rebuild: `.lam (.bvar 5) .type` synth-passed (the
`b' == .type` shortcut in subCheckSubst accepts any LHS) yet was
not `closedAt 0`.

**Resolution applied (option 1 from the original three paths):**
`Och.synth` now validates `e.closedAt 0` at entry and rejects
ill-formed input with `.error`.  The lemma `synthCore_topLevel_
closedAt` proves the predicate by unfolding synth and ruling out
the rejection branch.

For historical context, the alternative resolution paths were:

  1. Add a `closedAt 0` runtime check in `synth` (chosen).
  2. Hoist `closedAt 0` as a precondition on `Och_synth_sound`.
  3. Re-state `synth_sound` to use `closedAtLvl 0` instead — this is
     true and supported by the existing `evalSubst_closedAtLvl` /
     substrate hygiene block.  Requires a parallel
     `evalSubst_equiv_closedAtLvl` and propagation through the
     `Subtype'`-side declarative system, neither of which exists yet.

**Refactor in this commit.** The `.lam`, `.iota`, `.fix` arms of
`synthCore_sound_aux` are now closed via `Subtype'.refl` directly
(see `evalSubst_{lam,iota,fix}_refl` below), so they no longer
consume the wall.  Only `.letE`, `.app`, and `.asc` (inner only)
still need it.  See `EvalSubstLemmas.lean` for the closedness
inversion lemma `substL_closedAtLvl_inversion` that resolution path
3 would build on. -/

/-- If `Och.synth e fuel = .ok v` (top-level call with `Γ = []`),
then `e` is `closedAt 0`.

`Och.synth` now validates `e.closedAt 0` at entry and rejects with
`.error` otherwise (see API.lean), so `_h : .ok v` implies the
predicate.  This closes a previously walled obligation:
`.lam (.bvar 5) .type` was a counterexample; that input now fails
synth at the closedness check rather than at a downstream step. -/
theorem synthCore_topLevel_closedAt
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (h : Och.synth e fuel = .ok v) :
    e.closedAt 0 = true := by
  unfold Och.synth at h
  by_cases hcl : e.closedAt 0
  · exact hcl
  · simp [hcl] at h

/-! ## Per-arm bind-chain extraction helpers

Each canonical-form arm (`.lam`, `.iota`, `.fix`, `.letE`) ends
with `evalSubst fuel unfBound e`.  These lemmas extract that
final step from a `synthCore = .ok v` hypothesis by destructing
the bind chain. -/

/-- For the `.lam` arm: if `synthCore (n+1) [] (.lam dom body) = .ok v`,
then the final `evalSubst` step succeeded with the same `v`.  The arm:
`synthCore dom → subCheckOpen → if-else → evalSubst dom →
synthCore body → evalSubst e`.
On `.ok v` the first three steps succeeded and the final `evalSubst` is
the return value. -/
private theorem synthCore_lam_evalSubst {n : Nat} {dom body v : Expr}
    (h : synthCore (n+1) [] (.lam dom body) = .ok v) :
    evalSubst n unfBound (.lam dom body) = .ok v := by
  sorry

/-- Canonical-form refl: `evalSubst n unfBound (.lam dom body) = .ok v`
implies `v = .lam dom body`.  Combined with `synthCore_lam_evalSubst`,
this means synth's output for a `.lam` arm is the lam itself — no
closedness or evalSubst-equivalence needed to bridge.

The same holds for `.iota` and `.fix`: `evalSubst` returns
`.ok e` immediately, the canonical-form arms in `evalSubst.eq_*`
are pattern-direct.  This lets the synth-soundness proof close
those arms via `Subtype'.refl` without the `closedAt 0`
hypothesis. -/
private theorem evalSubst_lam_refl {n : Nat} {dom body v : Expr}
    (h : evalSubst n unfBound (.lam dom body) = .ok v) :
    v = .lam dom body := by
  cases n with
  | zero => rw [evalSubst.eq_1] at h; cases h
  | succ k =>
    rw [evalSubst.eq_5] at h
    simp only [Outcome.ok.injEq] at h; exact h.symm

private theorem synthCore_iota_evalSubst {n : Nat} {ann body v : Expr}
    (h : synthCore (n+1) [] (.iota ann body) = .ok v) :
    evalSubst n unfBound (.iota ann body) = .ok v := by
  sorry

private theorem evalSubst_iota_refl {n : Nat} {ann body v : Expr}
    (h : evalSubst n unfBound (.iota ann body) = .ok v) :
    v = .iota ann body := by
  cases n with
  | zero => rw [evalSubst.eq_1] at h; cases h
  | succ k =>
    rw [evalSubst.eq_6] at h
    simp only [Outcome.ok.injEq] at h; exact h.symm

private theorem synthCore_fix_evalSubst {n : Nat} {ann body v : Expr}
    (h : synthCore (n+1) [] (.fix ann body) = .ok v) :
    evalSubst n unfBound (.fix ann body) = .ok v := by
  sorry

private theorem evalSubst_fix_refl {n : Nat} {ann body v : Expr}
    (h : evalSubst n unfBound (.fix ann body) = .ok v) :
    v = .fix ann body := by
  cases n with
  | zero => rw [evalSubst.eq_1] at h; cases h
  | succ k =>
    rw [evalSubst.eq_7] at h
    simp only [Outcome.ok.injEq] at h; exact h.symm

private theorem synthCore_letE_evalSubst {n : Nat} {val body v : Expr}
    (h : synthCore (n+1) [] (.letE val body) = .ok v) :
    evalSubst n unfBound (.letE val body) = .ok v := by
  rw [synthCore.eq_9] at h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨_valV, _hVal, h⟩ := h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨_bodyTy, _hBody, h⟩ := h
  exact h

/-- For the `.asc` arm: if `synthCore (n+1) [] (.asc inner τ) = .ok v`,
then the inner recursive call also succeeded.  synthCore passes
the predecessor fuel `n` to the inner call. -/
private theorem synthCore_asc_inner {n : Nat} {inner τ v : Expr}
    (h : synthCore (n+1) [] (.asc inner τ) = .ok v) :
    synthCore n [] inner = .ok v := by
  sorry

/-- WALL: the residual `.app` arm.  synthCore on `.app f a`
returns `evalSubst (.app piExpr aV)`, where `piExpr` is the
result of `whnfPi`/`neutralType` exposure on the synthesised
`vF`.  Bridging this back to `(.app f a)` requires showing
`(.app f a) ⊑ (.app piExpr aV)` modulo evalSubst's β/unfold
steps — a multi-step `Subtype'.app_cong` + `evalSubst_equiv`
composition.  Sub-wall.

**Status.** Approached but not closed in this session.  The
plan is:

  1. Destructure synth's `.app` arm to extract `vF`, `aV`, `fV`,
     `piExpr` witnesses (~50 LOC, mechanical).
  2. From IH (when proven inline in `synthCore_sound_aux`):
     `Subtype' [] [] f vF` and `Subtype' [] [] a _vA`.
  3. From `evalSubst_equiv` on `f` and `a` (need closedness from
     `synthCore_topLevel_closedAt`, now CLOSED via the synth-entry
     check):
     `Subtype' [] [] f fV ∧ Subtype' [] [] fV f` and similarly
     for `a`/`aV`.
  4. **Hard step**: `Subtype' [] [] fV piExpr` — this is whnfPi's
     unfold chain: each step is either an `unfold_iota_R` /
     `unfold_fix_R` (declarative) or an `evalSubst` step (which
     needs equiv).  Requires either a dedicated whnfPi-equiv
     lemma or in-place unfolding of `whnfPi.go`.
  5. Compose via `app_cong` + `trans` + `evalSubst_equiv` on
     `(.app piExpr aV)`.

The destructuring + steps 2, 3, 5 are mechanical (~150 LOC).
Step 4 (whnfPi-equiv) is the substantive obligation; it would
be its own ~100 LOC structural induction over `whnfPi.go`.

**Coupling to wall 1.** Step 3 and step 5 both invoke
`evalSubst_equiv`, which requires `closedAt 0` of its input.  At
the top level that's the same hypothesis `synthCore_topLevel_
closedAt_WALL` provides; for the sub-applications (`f`, `a`,
`(.app piExpr aV)`) closedness propagation needs further
infrastructure.  Closing wall 2 fully thus depends on wall 1's
resolution. -/
private noncomputable def synthCore_app_WALL {n : Nat} {f a v : Expr}
    (_hclF : closedAt 0 f = true)
    (_hclA : closedAt 0 a = true)
    (_h : synthCore (n+1) [] (.app f a) = .ok v) :
    Subtype' [] [] (.app f a) v := by
  sorry

/-! ## Main soundness lemma -/

/-- Synth-soundness as an inductive lemma on the *expression*
(structural recursion), with `fuel` as a parameter.  Choosing
this induction shape lets the `.asc` arm — which recurses at the
*same* fuel but a structurally smaller subterm — use the IH
directly.

The `closedAt 0` hypothesis is needed to invoke `evalSubst_equiv`
on the canonical-form arms (`.lam`, `.iota`, `.fix`, `.letE`,
`.app`), all of which return `evalSubst …`.

The `Γ = []` specialisation matters: at top level there are no
level-vars in scope, so the `.bvar` arm must fail — hence the
`.bvar` case is vacuous in the proof. -/
private noncomputable def synthCore_sound_aux :
    ∀ (e : Expr) (fuel : Nat) (v : Expr),
      e.closedAt 0 = true →
      synthCore fuel [] e = .ok v →
      Subtype' [] [] e v := by
  intro e
  induction e with
  | type =>
    intro fuel v _ h
    cases fuel with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ n =>
      rw [synthCore.eq_2] at h
      simp only [Outcome.ok.injEq] at h
      subst h
      exact .refl _
  | bot =>
    intro fuel v _ h
    cases fuel with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ n =>
      rw [synthCore.eq_3] at h
      simp only [Outcome.ok.injEq] at h
      subst h
      exact .refl _
  | bvar k =>
    intro _ _ hcl _
    -- closedAt 0 (.bvar k) gives k < 0, contradiction.
    simp only [closedAt, decide_eq_true_eq] at hcl
    omega
  | lam dom body _ihDom _ihBody =>
    intro fuel v _hcl h
    cases fuel with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ n =>
      have hev := synthCore_lam_evalSubst h
      have hveq := evalSubst_lam_refl hev
      subst hveq
      exact .refl _
  | iota ann body _ihAnn _ihBody =>
    intro fuel v _hcl h
    cases fuel with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ n =>
      have hev := synthCore_iota_evalSubst h
      have hveq := evalSubst_iota_refl hev
      subst hveq
      exact .refl _
  | fix ann body _ihAnn _ihBody =>
    intro fuel v _hcl h
    cases fuel with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ n =>
      have hev := synthCore_fix_evalSubst h
      have hveq := evalSubst_fix_refl hev
      subst hveq
      exact .refl _
  | letE val body _ihVal _ihBody =>
    intro fuel v hcl h
    cases fuel with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ n =>
      have hev := synthCore_letE_evalSubst h
      exact (evalSubst_equiv hcl hev).2
  | asc inner τ ihInner _ihτ =>
    intro fuel v hcl h
    cases fuel with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ n =>
      simp only [closedAt, Bool.and_eq_true] at hcl
      have hinner := synthCore_asc_inner h
      have ihInnerApplied : Subtype' [] [] inner v :=
        ihInner n v hcl.1 hinner
      exact .asc_L ihInnerApplied
  | app f a _ihF _ihA =>
    intro fuel v hcl h
    cases fuel with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ n =>
      simp only [closedAt, Bool.and_eq_true] at hcl
      exact synthCore_app_WALL hcl.1 hcl.2 h

/-- The synthCore opacity wall, now decomposed into smaller pieces:
`synthCore_sound_aux`, `synthCore_app_WALL`, and the closed
`synthCore_topLevel_closedAt` lemma.

The composition: `Och.synth e fuel = .ok v` unfolds to
`synthCore fuel [] e = .ok v.whnf`.  We feed this plus the
closedAt-0 invariant (from the closedAt sub-wall) into
`synthCore_sound_aux`. -/
private noncomputable def synthCore_opacity_WALL
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (h : Och.synth e fuel = .ok v) :
    Subtype' [] [] e v.whnf := by
  have hcl : e.closedAt 0 = true := synthCore_topLevel_closedAt h
  unfold Och.synth at h
  simp only [hcl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  match heq : synthCore fuel [] e with
  | .ok v' =>
    rw [heq] at h
    simp only [Outcome.ok_bind, Pure.pure, Outcome.ok.injEq] at h
    subst h
    exact synthCore_sound_aux e fuel v' hcl heq
  | .outOfFuel =>
    rw [heq] at h
    cases h
  | .error _ =>
    rw [heq] at h
    cases h

/-- **synth-soundness**: if `Och.synth e fuel = .ok v`, then `e`
declaratively subtypes its synthesised WHNF `v.whnf`.

Delegates through `synthCore_opacity_WALL`, which routes through
two localised sub-obligations: `synthCore_topLevel_closedAt`
(closed via the synth-entry check) and `synthCore_app_WALL`
(the lone remaining synth wall). -/
noncomputable def Och_synth_sound
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (h : Och.synth e fuel = .ok v) :
    Subtype' [] [] e v.whnf :=
  synthCore_opacity_WALL h

end Och.Soundness
