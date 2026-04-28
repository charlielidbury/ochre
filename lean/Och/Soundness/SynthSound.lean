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

/-! ## closedAt-0 propagation (sub-wall) — DISCOVERED FALSE in general

The wall asserts `Och.synth e fuel = .ok v → e.closedAt 0 = true`.
**This is unsound as stated.**  Counterexample:

```
e := .lam (.bvar 5) .type
```

Trace through `synthCore` at `Γ = #[]`:

* `subCheckOpen #[] (.bvar 5) .type` → `evalSubst (.bvar 5)` returns
  `.ok (.bvar 5)` (substrate's bvar arm passes any non-level-var
  through unchanged), `evalSubst .type → .ok .type`, then
  `subCheckSubst` short-circuits via `b' == .type` → `.ok true`.  No
  closedness check.
* `evalSubst (.bvar 5)` succeeds (returns the bvar).
* `openFreshTop .type 0 = .type`, recursive synthCore on `.type`
  succeeds.
* Final `evalSubst (.lam (.bvar 5) .type)` returns the lam itself.

So `Och.synth (.lam (.bvar 5) .type) = .ok ⟨.lam (.bvar 5) .type⟩`,
yet `(.lam (.bvar 5) .type).closedAt 0 = false`.

**Why**: synth doesn't validate closedness of `dom` (lam-annotation)
or `ann` (iota/fix annotations); these only pass through
`subCheckOpen`, which itself doesn't enforce closedness — the
`b' == .type` shortcut accepts any LHS against `.type`.

**Resolution paths** (all out of scope for this commit):

  1. Add a `closedAt 0` runtime check in `synthCore` (touches
     `API.lean`, forbidden by current task constraints).
  2. Hoist `closedAt 0` as a precondition on `Och_synth_sound` and
     `synth_sound` (touches `Soundness.lean`, forbidden).
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

/-- WALL (false-as-stated; see module note above): if `Och.synth e
fuel = .ok v` (top-level call with `Γ = #[]`), then `e` is
`closedAt 0`.  Counterexample: `e = .lam (.bvar 5) .type`.

Stays as a sorry pending one of the three resolution paths in the
module note. -/
private theorem synthCore_topLevel_closedAt_WALL
    {fuel : Nat} {e : Expr} {v : Och.WTValue}
    (_h : Och.synth e fuel = .ok v) :
    e.closedAt 0 = true := by
  -- WALL: false in general; see module note.  Counterexample:
  -- `.lam (.bvar 5) .type` synth-passes but is not `closedAt 0`.
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

private theorem evalSubst_iota_refl {n : Nat} {ann body v : Expr}
    (h : evalSubst n unfBound (.iota ann body) = .ok v) :
    v = .iota ann body := by
  cases n with
  | zero => rw [evalSubst.eq_1] at h; cases h
  | succ k =>
    rw [evalSubst.eq_6] at h
    simp only [Outcome.ok.injEq] at h; exact h.symm

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

private theorem evalSubst_fix_refl {n : Nat} {ann body v : Expr}
    (h : evalSubst n unfBound (.fix ann body) = .ok v) :
    v = .fix ann body := by
  cases n with
  | zero => rw [evalSubst.eq_1] at h; cases h
  | succ k =>
    rw [evalSubst.eq_7] at h
    simp only [Outcome.ok.injEq] at h; exact h.symm

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
composition.  Sub-wall.

**Status.** Approached but not closed in this session.  The
plan is:

  1. Destructure synth's `.app` arm to extract `vF`, `aV`, `fV`,
     `piExpr` witnesses (~50 LOC, mechanical).
  2. From IH (when proven inline in `synthCore_sound_aux`):
     `Subtype' [] [] f vF` and `Subtype' [] [] a _vA`.
  3. From `evalSubst_equiv` on `f` and `a` (need closedness from
     the also-walled `synthCore_topLevel_closedAt_WALL`):
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
