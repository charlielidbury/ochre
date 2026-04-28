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
    (whnfPi may unfold further).

  * `synthCore_topLevel_closedAt_WALL` — propagating `closedAt 0`
    from synth-acceptance back through binder bodies.  At top-level
    `Γ = #[]`, a free `bvar` would fail the `.bvar` arm, so synth
    only accepts `closedAt 0` inputs; the discharge requires
    structural inversion through `openFreshTop` substitution.

These two walls are the residue of the previous monolithic
`synthCore_opacity_WALL` — they are strictly weaker (smaller
surface, more localised) and each is a self-contained obligation.
-/

namespace Och.Soundness

open SubstEval
open Expr (closedAt closedAtLvl noLevelVars)

/-! ## closedAt-0 propagation (sub-wall)

`Och.synth e fuel = .ok v` only succeeds when every recursive
call site (binder bodies, `.asc` inner, `.app` f/a, `.letE` val/
body) accepts; and at the *top* level `Γ = #[]`, so any free
`bvar` in `e` would fail the `.bvar` arm.  Hence top-level
synth acceptance implies `e.closedAt 0 = true`.

To prove this for *every* recursive call, we'd need to show that
`openFreshTop body depth` and `Γ.push annV` keep the closedAt
invariant.  The substrate has the relevant lemmas
(`Expr.subst_closedAt`, `bvarLT_of_closedAt`) but threading them
through the synth-accept witness requires a dedicated structural
induction.

We isolate this as a single sub-wall and use it at the top-level
call site only. -/

/-- WALL: if `Och.synth e fuel = .ok v` (top-level call with
`Γ = #[]`), then `e` is `closedAt 0`.  This is the closedAt
invariant the inner `synthCore_sound_aux` needs. -/
private theorem synthCore_topLevel_closedAt_WALL
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (_h : Och.synth e fuel = .ok v) :
    e.closedAt 0 = true := by
  -- WALL: structural inversion through openFreshTop / Γ.push.
  -- At top-level `Γ = #[]`, the `.bvar` arm always fails (the
  -- `lvl < Γ.size` check fails for any level-var).  Pushing
  -- this through the binder arms requires
  -- `(openFreshTop body 0).closedAt 0 → body.closedAt 1`, which
  -- is a routine substitution lemma we leave as a sorry-stub.
  sorry

/-! ## Per-arm bind-chain extraction helpers

Each canonical-form arm (`.lam`, `.iota`, `.fix`, `.letE`) ends
with `evalSubst fuel unfBound e`.  These lemmas extract that
final step from a `synthCore = .ok v` hypothesis by destructing
the bind chain. -/

/-- For the `.lam` arm: if `synthCore (n+1) #[] (.lam dom body) = .ok v`,
then the final `evalSubst` step succeeded with the same `v`.  The arm:
`subCheckOpen → if-else → evalSubst dom → synthCore body → evalSubst e`.
On `.ok v` the first three steps succeeded and the final `evalSubst` is
the return value. -/
private theorem synthCore_lam_evalSubst {n : Nat} {dom body v : Expr}
    (h : synthCore (n+1) #[] (.lam dom body) = .ok v) :
    evalSubst n unfBound (.lam dom body) = .ok v := by
  rw [synthCore.eq_5] at h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨okDom, _hSub, h⟩ := h
  by_cases hok : okDom
  · simp only [hok, Bool.not_true, Bool.false_eq_true, if_false] at h
    rw [Outcome.bind_eq_ok] at h
    obtain ⟨_domV, _hDom, h⟩ := h
    rw [Outcome.bind_eq_ok] at h
    obtain ⟨_bodyTy, _hBody, h⟩ := h
    exact h
  · simp only [Bool.not_eq_true] at hok
    subst hok
    simp only [Bool.not_false, if_true] at h
    cases h

private theorem synthCore_iota_evalSubst {n : Nat} {ann body v : Expr}
    (h : synthCore (n+1) #[] (.iota ann body) = .ok v) :
    evalSubst n unfBound (.iota ann body) = .ok v := by
  rw [synthCore.eq_6] at h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨okAnn, _hSub, h⟩ := h
  by_cases hok : okAnn
  · simp only [hok, Bool.not_true, Bool.false_eq_true, if_false] at h
    rw [Outcome.bind_eq_ok] at h
    obtain ⟨_annV, _hAnn, h⟩ := h
    rw [Outcome.bind_eq_ok] at h
    obtain ⟨_bodyTy, _hBody, h⟩ := h
    exact h
  · simp only [Bool.not_eq_true] at hok
    subst hok
    simp only [Bool.not_false, if_true] at h
    cases h

private theorem synthCore_fix_evalSubst {n : Nat} {ann body v : Expr}
    (h : synthCore (n+1) #[] (.fix ann body) = .ok v) :
    evalSubst n unfBound (.fix ann body) = .ok v := by
  rw [synthCore.eq_7] at h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨okAnn, _hSub, h⟩ := h
  by_cases hok : okAnn
  · simp only [hok, Bool.not_true, Bool.false_eq_true, if_false] at h
    rw [Outcome.bind_eq_ok] at h
    obtain ⟨_annV, _hAnn, h⟩ := h
    rw [Outcome.bind_eq_ok] at h
    obtain ⟨_bodyTy, _hBody, h⟩ := h
    exact h
  · simp only [Bool.not_eq_true] at hok
    subst hok
    simp only [Bool.not_false, if_true] at h
    cases h

private theorem synthCore_letE_evalSubst {n : Nat} {val body v : Expr}
    (h : synthCore (n+1) #[] (.letE val body) = .ok v) :
    evalSubst n unfBound (.letE val body) = .ok v := by
  rw [synthCore.eq_9] at h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨_valV, _hVal, h⟩ := h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨_bodyTy, _hBody, h⟩ := h
  exact h

/-- For the `.asc` arm: if `synthCore (n+1) #[] (.asc inner τ) = .ok v`,
then the inner recursive call also succeeded.  synthCore passes
the predecessor fuel `n` to the inner call. -/
private theorem synthCore_asc_inner {n : Nat} {inner τ v : Expr}
    (h : synthCore (n+1) #[] (.asc inner τ) = .ok v) :
    synthCore n #[] inner = .ok v := by
  rw [synthCore.eq_8] at h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨okτ, _hτCheck, h⟩ := h
  by_cases hok : okτ
  · simp only [hok, Bool.not_true, Bool.false_eq_true, if_false] at h
    rw [Outcome.bind_eq_ok] at h
    obtain ⟨_τV, _hτV, h⟩ := h
    rw [Outcome.bind_eq_ok] at h
    obtain ⟨_vInner, hInner, h⟩ := h
    rw [Outcome.bind_eq_ok] at h
    obtain ⟨okFinal, _hCheck, h⟩ := h
    by_cases hokF : okFinal
    · simp only [hokF, Bool.not_true, Bool.false_eq_true, if_false] at h
      simp only [Outcome.ok.injEq] at h
      subst h
      exact hInner
    · simp only [Bool.not_eq_true] at hokF
      subst hokF
      simp only [Bool.not_false, if_true] at h
      cases h
  · simp only [Bool.not_eq_true] at hok
    subst hok
    simp only [Bool.not_false, if_true] at h
    cases h

/-- WALL: the residual `.app` arm.  synthCore on `.app f a`
returns `evalSubst (.app piExpr aV)`, where `piExpr` is the
result of `whnfPi`/`neutralType` exposure on the synthesised
`vF`.  Bridging this back to `(.app f a)` requires showing
`(.app f a) ⊑ (.app piExpr aV)` modulo evalSubst's β/unfold
steps — a multi-step `Subtype'.app_cong` + `evalSubst_equiv`
composition.  Sub-wall. -/
private theorem synthCore_app_WALL {n : Nat} {f a v : Expr}
    (_hclF : closedAt 0 f = true)
    (_hclA : closedAt 0 a = true)
    (_h : synthCore (n+1) #[] (.app f a) = .ok v) :
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

The `Γ = #[]` specialisation matters: at top level there are no
level-vars in scope, so the `.bvar` arm must fail — hence the
`.bvar` case is vacuous in the proof. -/
private theorem synthCore_sound_aux :
    ∀ (e : Expr) (fuel : Nat) (v : Expr),
      e.closedAt 0 = true →
      synthCore fuel #[] e = .ok v →
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
    intro fuel v hcl h
    cases fuel with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ n =>
      have hev := synthCore_lam_evalSubst h
      exact (evalSubst_equiv hcl hev).2
  | iota ann body _ihAnn _ihBody =>
    intro fuel v hcl h
    cases fuel with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ n =>
      have hev := synthCore_iota_evalSubst h
      exact (evalSubst_equiv hcl hev).2
  | fix ann body _ihAnn _ihBody =>
    intro fuel v hcl h
    cases fuel with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ n =>
      have hev := synthCore_fix_evalSubst h
      exact (evalSubst_equiv hcl hev).2
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

/-- **WALL** (legacy name): the synthCore opacity wall.  This
theorem is now decomposed into smaller pieces — see
`synthCore_sound_aux`, `synthCore_app_WALL`, and
`synthCore_topLevel_closedAt_WALL` above — each a localised
sub-wall.

The composition: `Och.synth e fuel = .ok v` unfolds to
`synthCore fuel #[] e = .ok v.whnf`.  We feed this plus the
closedAt-0 invariant (from the closedAt sub-wall) into
`synthCore_sound_aux`. -/
private theorem synthCore_opacity_WALL
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (h : Och.synth e fuel = .ok v) :
    Subtype' [] [] e v.whnf := by
  have hcl : e.closedAt 0 = true := synthCore_topLevel_closedAt_WALL h
  unfold Och.synth at h
  match heq : synthCore fuel #[] e with
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

Currently delegated through `synthCore_opacity_WALL`, which now
routes through three smaller localised sub-walls
(`synthCore_topLevel_closedAt_WALL`, `synthCore_app_WALL`, and
the per-arm bind-chain extractors which are fully discharged). -/
theorem Och_synth_sound
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (h : Och.synth e fuel = .ok v) :
    Subtype' [] [] e v.whnf :=
  synthCore_opacity_WALL h

end Och.Soundness
