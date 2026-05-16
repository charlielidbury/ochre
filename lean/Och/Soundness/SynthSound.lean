import Och.Syntax
import Och.EvalSubst
import Och.Subtyping
import Och.API
import Och.Soundness.EvalSubstEquiv
import Och.Soundness.SubCheckSubstSoundness

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

## Status: sorry-free

All arms are closed. The former last wall (`synthCore_app_WALL`
neutralType fallback) was closed by generalizing `whnfPi_sound` to
open contexts (`whnfPi_sound_open` in SubCheckSubstSoundness.lean)
and proving `synthNeutralType_to_sub` for `.app` via fuel induction
+ `whnfPi_sound_open` + `app_elim` + `evalSubst_equiv_open`.

## Closed walls

  * `whnfPi_go_sound` iota case (Option B): Changed the proof strategy
    from "e ⊑ piExpr" to "inhab ⊑ piExpr" with precondition "inhab ⊑ e".
    For the iota case, `iota_elim` gives `inhab ⊑ body[self↦inhab]`,
    which is exactly what the algorithm evaluates. No algorithm change
    needed.

  * `whnfPi_go_sound` fix case: `(.fix ann body) ⊑ piExpr` via
    `unfold_fix_L` + `evalSubst_equiv` + IH.

  * `synthCore_app_WALL` primary path (direct `whnfPi` exposure):
    fully closed. The 3-step chain
    `(.app f a) ⊑ (.app fV aV) ⊑ (.app piExpr aV) ⊑ v`
    is established via `app_cong`, `whnfPi_sound` (Option B),
    and `evalSubst_equiv` respectively.
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
  rw [synthCore.eq_5] at h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨okDom, hOkDom, h⟩ := h
  split at h <;> try cases h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨domV, hDomV, h⟩ := h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨_bodyTy, _hBody, h⟩ := h
  exact h

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
  rw [synthCore.eq_6] at h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨okAnn, hOkAnn, h⟩ := h
  split at h <;> try cases h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨annV, hAnnV, h⟩ := h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨_bodyTy, _hBody, h⟩ := h
  exact h

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
  rw [synthCore.eq_7] at h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨okAnn, hOkAnn, h⟩ := h
  split at h <;> try cases h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨annV, hAnnV, h⟩ := h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨_bodyTy, _hBody, h⟩ := h
  exact h

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
  rw [synthCore.eq_8] at h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨okτ, _hOkτ, h⟩ := h
  split at h <;> try cases h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨_τV, _hτV, h⟩ := h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨vInner, hInner, h⟩ := h
  rw [Outcome.bind_eq_ok] at h
  obtain ⟨ok, _hOk, h⟩ := h
  split at h
  · cases h
  · simp only [Outcome.ok.injEq] at h
    subst h
    exact hInner

/-! ## Closedness preservation for synthCore and whnfPi -/

/-- `whnfPi.go` preserves `closedAt 0`: if the input expression and
inhabitant are closed, the output is closed. -/
private theorem whnfPi_go_closedAt (fuel : Nat) (inhab : Expr)
    (hcl_inhab : closedAt 0 inhab = true)
    : ∀ (n : Nat) (e piExpr : Expr),
      closedAt 0 e = true →
      whnfPi.go fuel inhab n e = some piExpr →
      closedAt 0 piExpr = true := by
  intro n
  induction n with
  | zero =>
    intro e piExpr hcl hgo
    simp only [whnfPi.go] at hgo
    injection hgo with hgo; subst hgo; exact hcl
  | succ m ih =>
    intro e piExpr hcl hgo
    match e with
    | .lam dom body =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hcl
    | .fix ann body =>
      simp only [whnfPi.go] at hgo
      match hev : evalSubst fuel 4 (body.subst 0 (.fix ann body)) with
      | .ok e' =>
        rw [hev] at hgo
        have hcl_fix : closedAt 0 (.fix ann body) = true := hcl
        simp only [closedAt, Bool.and_eq_true] at hcl
        have hcl_subst : closedAt 0 (body.subst 0 (.fix ann body)) = true :=
          Expr.subst_closedAt (by simpa using hcl.2) hcl_fix
        have hcl_e' := SubstEval.evalSubst_closedAt hcl_subst hev
        exact ih e' piExpr hcl_e' hgo
      | .outOfFuel => rw [hev] at hgo; cases hgo
      | .error _ => rw [hev] at hgo; cases hgo
    | .iota _ann _body =>
      simp only [whnfPi.go] at hgo
      match hev : evalSubst fuel 4 (_body.subst 0 inhab) with
      | .ok e' =>
        rw [hev] at hgo
        simp only [closedAt, Bool.and_eq_true] at hcl
        have hcl_subst : closedAt 0 (_body.subst 0 inhab) = true :=
          Expr.subst_closedAt (by simpa using hcl.2) hcl_inhab
        have hcl_e' := SubstEval.evalSubst_closedAt hcl_subst hev
        exact ih e' piExpr hcl_e' hgo
      | .outOfFuel => rw [hev] at hgo; cases hgo
      | .error _ => rw [hev] at hgo; cases hgo
    | .bot => simp only [whnfPi.go] at hgo; cases hgo
    | .bvar _ =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hcl
    | .type =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hcl
    | .app _ _ =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hcl
    | .asc _ _ =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hcl
    | .letE _ _ =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hcl

/-- `whnfPi` preserves `closedAt 0`: if the input type and inhabitant
are closed, the output is closed. -/
private theorem whnfPi_closedAt {n : Nat} {inhab ty piExpr : Expr}
    (hcl_ty : closedAt 0 ty = true)
    (hcl_inhab : closedAt 0 inhab = true)
    (h : whnfPi n inhab ty = some piExpr) :
    closedAt 0 piExpr = true := by
  unfold whnfPi at h
  match hev : evalSubst n SubstEval.unfBound ty with
  | .ok ty' =>
    rw [hev] at h
    have hcl_ty' := SubstEval.evalSubst_closedAt hcl_ty hev
    exact whnfPi_go_closedAt n inhab hcl_inhab SubstEval.unfBound ty' piExpr hcl_ty' h
  | .outOfFuel => rw [hev] at h; cases h
  | .error _ => rw [hev] at h; cases h

/-- `neutralType` (= `synthNeutralType`) preserves `closedAt 0`
for the empty context. Uses `exposePi_eq_whnfPi` to bridge the
private `exposePi` (used by `synthNeutralType`) to the public
`whnfPi` (for which we have `whnfPi_closedAt`). -/
private theorem neutralType_closedAt {fuel : Nat} {e ty : Expr}
    (hcl : closedAt 0 e = true)
    (h : neutralType fuel [] e = .ok (some ty)) :
    closedAt 0 ty = true := by
  unfold neutralType at h
  induction fuel generalizing e ty with
  | zero => unfold synthNeutralType at h; cases h
  | succ k ih =>
    unfold synthNeutralType at h
    match e with
    | .bvar j =>
      simp only [] at h
      simp only [List.get?] at h
      cases h
    | .fix ann _ =>
      simp only [] at h
      match hev : evalSubst (k + 1) SubstEval.unfBound ann with
      | .ok ann' =>
        rw [hev] at h
        simp only [Outcome.ok.injEq, Option.some.injEq] at h
        subst h
        simp only [closedAt, Bool.and_eq_true] at hcl
        exact SubstEval.evalSubst_closedAt hcl.1 hev
      | .outOfFuel => rw [hev] at h; simp at h
      | .error _ => rw [hev] at h; simp at h
    | .app f arg =>
      simp only [] at h
      simp only [closedAt, Bool.and_eq_true] at hcl
      match hnt : synthNeutralType k [] f with
      | .outOfFuel => rw [hnt] at h; cases h
      | .error _ => rw [hnt] at h; cases h
      | .ok none =>
        rw [hnt] at h; simp only [Outcome.ok_bind] at h; cases h
      | .ok (some tyF) =>
        rw [hnt] at h; simp only [Outcome.ok_bind] at h
        have hnt' : neutralType k [] f = .ok (some tyF) := hnt
        have hcl_tyF : closedAt 0 tyF = true := ih hcl.1 hnt'
        -- Rewrite exposePi✝ to whnfPi via the bridge lemma
        rw [exposePi_eq_whnfPi] at h
        -- Use split to handle the match on whnfPi result
        split at h
        · -- whnfPi returned some (.lam _dom retTy)
          rename_i _dom retTy hwp
          have hcl_piExpr := whnfPi_closedAt hcl_tyF hcl.1 hwp
          simp only [closedAt, Bool.and_eq_true] at hcl_piExpr
          have hcl_subst : closedAt 0 (retTy.subst 0 arg) = true :=
            Expr.subst_closedAt (by simpa using hcl_piExpr.2) hcl.2
          split at h
          · -- evalSubst succeeded
            rename_i r hev
            simp only [Outcome.ok.injEq, Option.some.injEq] at h
            subst h
            exact SubstEval.evalSubst_closedAt hcl_subst hev
          · -- evalSubst failed
            simp at h
        · -- whnfPi returned something else
          simp at h
    | .type => simp only [] at h; cases h
    | .bot => simp only [] at h; cases h
    | .lam _ _ => simp only [] at h; cases h
    | .iota _ _ => simp only [] at h; cases h
    | .asc _ _ => simp only [] at h; cases h
    | .letE _ _ => simp only [] at h; cases h

/-- `synthCore` preserves `closedAt 0` on closed inputs.
Each canonical arm returns `evalSubst e` (covered by `evalSubst_closedAt`);
`.asc` recurses; `.app` composes whnfPi closedness + evalSubst closedness. -/
private theorem synthCore_closedAt {n : Nat} {e v : Expr}
    (hcl : closedAt 0 e = true)
    (h : synthCore n [] e = .ok v) :
    closedAt 0 v = true := by
  induction e generalizing n v with
  | type =>
    cases n with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ k =>
      rw [synthCore.eq_2] at h
      simp only [Outcome.ok.injEq] at h; subst h
      simp [closedAt]
  | bot =>
    cases n with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ k =>
      rw [synthCore.eq_3] at h
      simp only [Outcome.ok.injEq] at h; subst h
      simp [closedAt]
  | bvar k =>
    -- closedAt 0 (.bvar k) gives k < 0, contradiction.
    simp only [closedAt, decide_eq_true_eq] at hcl; omega
  | lam dom body _ihDom _ihBody =>
    cases n with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ k =>
      have hev := synthCore_lam_evalSubst h
      have hveq := evalSubst_lam_refl hev
      subst hveq; exact hcl
  | iota ann body _ihAnn _ihBody =>
    cases n with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ k =>
      have hev := synthCore_iota_evalSubst h
      have hveq := evalSubst_iota_refl hev
      subst hveq; exact hcl
  | fix ann body _ihAnn _ihBody =>
    cases n with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ k =>
      have hev := synthCore_fix_evalSubst h
      have hveq := evalSubst_fix_refl hev
      subst hveq; exact hcl
  | letE val body _ihVal _ihBody =>
    cases n with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ k =>
      have hev := synthCore_letE_evalSubst h
      exact SubstEval.evalSubst_closedAt hcl hev
  | asc inner τ ihInner _ihτ =>
    cases n with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ k =>
      simp only [closedAt, Bool.and_eq_true] at hcl
      have hinner := synthCore_asc_inner h
      exact ihInner hcl.1 hinner
  | app f a ihF _ihA =>
    cases n with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ k =>
      simp only [closedAt, Bool.and_eq_true] at hcl
      rw [synthCore.eq_10] at h
      -- Destructure the bind chain
      match hvF_eq : synthCore k [] f with
      | .outOfFuel => rw [hvF_eq] at h; cases h
      | .error _ => rw [hvF_eq] at h; cases h
      | .ok vF =>
      rw [hvF_eq] at h; simp only [Outcome.ok_bind] at h
      match hvA_eq : synthCore k [] a with
      | .outOfFuel => rw [hvA_eq] at h; cases h
      | .error _ => rw [hvA_eq] at h; cases h
      | .ok _vA =>
      rw [hvA_eq] at h; simp only [Outcome.ok_bind] at h
      match haV_eq : evalSubst k SubstEval.unfBound a with
      | .outOfFuel => rw [haV_eq] at h; cases h
      | .error _ => rw [haV_eq] at h; cases h
      | .ok aV =>
      rw [haV_eq] at h; simp only [Outcome.ok_bind] at h
      match hfV_eq : evalSubst k SubstEval.unfBound f with
      | .outOfFuel => rw [hfV_eq] at h; cases h
      | .error _ => rw [hfV_eq] at h; cases h
      | .ok fV =>
      rw [hfV_eq] at h; simp only [Outcome.ok_bind] at h
      have hcl_fV := SubstEval.evalSubst_closedAt hcl.1 hfV_eq
      have hcl_aV := SubstEval.evalSubst_closedAt hcl.2 haV_eq
      have hcl_vF := ihF hcl.1 hvF_eq
      -- After the four initial bind extractions (synthCore f/a, evalSubst a/f),
      -- h is a fully-inlined match on whnfPi. Use split to dispatch.
      split at h
      · -- Primary path: whnfPi returned some (.lam piDom piBody)
        rename_i piLam piDom piBody hwp
        have hcl_piExpr := whnfPi_closedAt hcl_vF hcl_fV hwp
        simp only [] at h
        match hdomChk : subCheckOpen k [] aV piDom with
        | .outOfFuel => rw [hdomChk] at h; cases h
        | .error _ => rw [hdomChk] at h; cases h
        | .ok true =>
          rw [hdomChk] at h; simp only [Outcome.ok_bind] at h
          have hcl_app_pi : closedAt 0 (.app (.lam piDom piBody) aV) = true := by
            simp only [closedAt, Bool.and_eq_true] at hcl_piExpr ⊢; exact ⟨hcl_piExpr, hcl_aV⟩
          exact SubstEval.evalSubst_closedAt hcl_app_pi h
        | .ok false =>
          rw [hdomChk] at h; simp only [Outcome.ok_bind] at h
          match hntA : neutralType k [] aV with
          | .ok (some aTy) =>
            rw [hntA] at h; simp only [Outcome.ok_bind] at h
            match hdomChk2 : subCheckOpen k [] aTy piDom with
            | .outOfFuel => rw [hdomChk2] at h; cases h
            | .error _ => rw [hdomChk2] at h; cases h
            | .ok true =>
              rw [hdomChk2] at h; simp only [Outcome.ok_bind] at h
              have hcl_app_pi : closedAt 0 (.app (.lam piDom piBody) aV) = true := by
                simp only [closedAt, Bool.and_eq_true] at hcl_piExpr ⊢; exact ⟨hcl_piExpr, hcl_aV⟩
              exact SubstEval.evalSubst_closedAt hcl_app_pi h
            | .ok false =>
              rw [hdomChk2] at h; simp only [Outcome.ok_bind] at h; cases h
          | .ok none =>
            rw [hntA] at h; simp only [Outcome.ok_bind] at h; cases h
          | .outOfFuel => rw [hntA] at h; cases h
          | .error _ => rw [hntA] at h; cases h
      · -- Secondary path: whnfPi returned something else.
        -- h is about the neutralType + whnfPi chain.
        -- Dispatch on neutralType result.
        rename_i _hwp
        match hntF : neutralType k [] vF with
        | .outOfFuel =>
          simp only [hntF, Outcome.outOfFuel_bind] at h; cases h
        | .error _ =>
          simp only [hntF, Outcome.error_bind] at h; cases h
        | .ok none =>
          simp only [hntF, Outcome.ok_bind] at h; cases h
        | .ok (some tyF) =>
          simp only [hntF, Outcome.ok_bind] at h
          have hcl_tyF := neutralType_closedAt hcl_vF hntF
          -- Now h is about whnfPi k fV tyF + domain check chain
          split at h
          · -- whnfPi returned .lam
            rename_i _piLam2 piDom2 piBody2 hwp2
            have hcl_piExpr2 := whnfPi_closedAt hcl_tyF hcl_fV hwp2
            simp only [] at h
            match hdomChk : subCheckOpen k [] aV piDom2 with
            | .outOfFuel => rw [hdomChk] at h; cases h
            | .error _ => rw [hdomChk] at h; cases h
            | .ok true =>
              rw [hdomChk] at h; simp only [Outcome.ok_bind] at h
              have hcl_app_pi : closedAt 0 (.app (.lam piDom2 piBody2) aV) = true := by
                simp only [closedAt, Bool.and_eq_true] at hcl_piExpr2 ⊢; exact ⟨hcl_piExpr2, hcl_aV⟩
              exact SubstEval.evalSubst_closedAt hcl_app_pi h
            | .ok false =>
              rw [hdomChk] at h; simp only [Outcome.ok_bind] at h
              match hntA : neutralType k [] aV with
              | .ok (some aTy) =>
                rw [hntA] at h; simp only [Outcome.ok_bind] at h
                match hdomChk2 : subCheckOpen k [] aTy piDom2 with
                | .outOfFuel => rw [hdomChk2] at h; cases h
                | .error _ => rw [hdomChk2] at h; cases h
                | .ok true =>
                  rw [hdomChk2] at h; simp only [Outcome.ok_bind] at h
                  have hcl_app_pi : closedAt 0 (.app (.lam piDom2 piBody2) aV) = true := by
                    simp only [closedAt, Bool.and_eq_true] at hcl_piExpr2 ⊢; exact ⟨hcl_piExpr2, hcl_aV⟩
                  exact SubstEval.evalSubst_closedAt hcl_app_pi h
                | .ok false =>
                  rw [hdomChk2] at h; simp only [Outcome.ok_bind] at h; cases h
              | .ok none =>
                rw [hntA] at h; simp only [Outcome.ok_bind] at h; cases h
              | .outOfFuel => rw [hntA] at h; cases h
              | .error _ => rw [hntA] at h; cases h
          · -- whnfPi returned non-lam → error
            cases h

/-! ## whnfPi soundness

`whnfPi fuel inhab ty` unfolds fix/iota wrappers in `ty` until a
`.lam` (Π) head is exposed.

**Strategy (Option B):** Instead of proving `e ⊑ piExpr` (which would
require substitution monotonicity for the iota case), we prove
`inhab ⊑ piExpr` given `inhab ⊑ e`. This works because:
- **Fix case:** `inhab ⊑ fix ⊑ body[self↦fix]` (via `unfold_fix_L`),
  then eval + IH.
- **Iota case:** `inhab ⊑ iota` + `iota_elim` gives
  `inhab ⊑ body[self↦inhab]`, which is exactly what the algorithm
  evaluates. Then eval + IH.
- **Other cases:** `go` returns `e` unchanged, so `inhab ⊑ e` suffices.

At the call site, this directly gives `fV ⊑ piExpr`, simplifying the
proof chain. -/

/-- Inner loop soundness: if `go n e = some piExpr` and `inhab ⊑ e`,
then `inhab ⊑ piExpr`. Both fix and iota cases are closed. -/
private noncomputable def whnfPi_go_sound
    (fuel : Nat) (inhab : Expr)
    (hcl_inhab : closedAt 0 inhab = true)
    : ∀ (n : Nat) (e piExpr : Expr),
      closedAt 0 e = true →
      Subtype' [] [] inhab e →
      whnfPi.go fuel inhab n e = some piExpr →
      Subtype' [] [] inhab piExpr := by
  intro n
  induction n with
  | zero =>
    intro e piExpr _hcl hsub hgo
    simp only [whnfPi.go] at hgo
    injection hgo with hgo; subst hgo; exact hsub
  | succ m ih =>
    intro e piExpr hcl hsub hgo
    match e with
    | .lam dom body =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub
    | .fix ann body =>
      simp only [whnfPi.go] at hgo
      match hev : evalSubst fuel 4 (body.subst 0 (.fix ann body)) with
      | .ok e' =>
        rw [hev] at hgo
        have hcl_fix : closedAt 0 (.fix ann body) = true := hcl
        simp only [closedAt, Bool.and_eq_true] at hcl
        have hcl_subst : closedAt 0 (body.subst 0 (.fix ann body)) = true :=
          Expr.subst_closedAt (by simpa using hcl.2) hcl_fix
        have hcl_e' := SubstEval.evalSubst_closedAt hcl_subst hev
        have ⟨_, hfwd⟩ := evalSubst_equiv hcl_subst hev
        -- fix ⊑ body.subst 0 fix (via unfold_fix_L + weaken from [])
        have step_unfold : Subtype' [] [] (.fix ann body)
            (body.subst 0 (.fix ann body)) :=
          .unfold_fix_L (Subtype'.weaken
            (fun _ hp => absurd hp (List.not_mem_nil _)) (.refl _))
        -- inhab ⊑ fix ⊑ body.subst fix ⊑ e'
        have hsub' : Subtype' [] [] inhab e' :=
          .trans hsub (.trans step_unfold hfwd)
        exact ih e' piExpr hcl_e' hsub' hgo
      | .outOfFuel => rw [hev] at hgo; cases hgo
      | .error _ => rw [hev] at hgo; cases hgo
    | .iota _ann _body =>
      simp only [whnfPi.go] at hgo
      match hev : evalSubst fuel 4 (_body.subst 0 inhab) with
      | .ok e' =>
        rw [hev] at hgo
        simp only [closedAt, Bool.and_eq_true] at hcl
        have hcl_subst : closedAt 0 (_body.subst 0 inhab) = true :=
          Expr.subst_closedAt (by simpa using hcl.2) hcl_inhab
        have hcl_e' := SubstEval.evalSubst_closedAt hcl_subst hev
        have ⟨_, hfwd⟩ := evalSubst_equiv hcl_subst hev
        -- inhab ⊑ iota, so iota_elim gives inhab ⊑ body[self↦inhab]
        have step_elim : Subtype' [] [] inhab (_body.subst 0 inhab) :=
          .iota_elim hsub
        -- inhab ⊑ body[self↦inhab] ⊑ e'
        have hsub' : Subtype' [] [] inhab e' :=
          .trans step_elim hfwd
        exact ih e' piExpr hcl_e' hsub' hgo
      | .outOfFuel => rw [hev] at hgo; cases hgo
      | .error _ => rw [hev] at hgo; cases hgo
    | .bot => simp only [whnfPi.go] at hgo; cases hgo
    | .bvar _ =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub
    | .type =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub
    | .app _ _ =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub
    | .asc _ _ =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub
    | .letE _ _ =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub

/-- Top-level `whnfPi` soundness: if `whnfPi fuel inhab ty = some piExpr`
and `inhab ⊑ ty`, then `inhab ⊑ piExpr`. Composes the initial
`evalSubst` step with `whnfPi_go_sound`. -/
private noncomputable def whnfPi_sound
    {fuel : Nat} {inhab ty piExpr : Expr}
    (hcl_ty : closedAt 0 ty = true)
    (hcl_inhab : closedAt 0 inhab = true)
    (hsub_inhab : Subtype' [] [] inhab ty)
    (h : whnfPi fuel inhab ty = some piExpr) :
    Subtype' [] [] inhab piExpr := by
  unfold whnfPi at h
  match hev : evalSubst fuel SubstEval.unfBound ty with
  | .ok ty' =>
    rw [hev] at h
    have hcl_ty' := SubstEval.evalSubst_closedAt hcl_ty hev
    have ⟨_, hfwd⟩ := evalSubst_equiv hcl_ty hev
    exact whnfPi_go_sound fuel inhab hcl_inhab
      SubstEval.unfBound ty' piExpr hcl_ty' (.trans hsub_inhab hfwd) h
  | .outOfFuel => rw [hev] at h; cases h
  | .error _ => rw [hev] at h; cases h

-- Open-context whnfPi soundness (`whnfPi_go_sound_open`, `whnfPi_sound_open`)
-- is in SubCheckSubstSoundness.lean, where `evalSubst_equiv_open` lives.

/-! ## The .app arm

The `.app` arm of synth-soundness composes a 3-step chain:

1. `(.app f a) ⊑ (.app fV aV)` via `app_cong` + `evalSubst_equiv`
2. `(.app fV aV) ⊑ (.app piExpr aV)` via `app_cong` + `whnfPi_sound`
   (Option B: `whnfPi_sound` proves `fV ⊑ piExpr` given `fV ⊑ vF`,
   composing iota_elim/unfold_fix_L with the eval bridge)
3. `(.app piExpr aV) ⊑ v` via `evalSubst_equiv` on the final eval

The proof destructures the bind chain of `synthCore.eq_10` inline,
matching on intermediate `Outcome` results. -/
private noncomputable def synthCore_app_WALL {n : Nat} {f a v : Expr}
    (hclF : closedAt 0 f = true)
    (hclA : closedAt 0 a = true)
    (h : synthCore (n+1) [] (.app f a) = .ok v)
    (ihF : ∀ (fuel : Nat) (v : Expr),
      closedAt 0 f = true → synthCore fuel [] f = .ok v →
      Subtype' [] [] f v) :
    Subtype' [] [] (.app f a) v := by
  -- Rewrite with the equation lemma
  rw [synthCore.eq_10] at h
  -- Destructure the bind chain by matching on intermediate results
  match hvF_eq : synthCore n [] f with
  | .outOfFuel => rw [hvF_eq] at h; cases h
  | .error _ => rw [hvF_eq] at h; cases h
  | .ok vF =>
  rw [hvF_eq] at h; simp only [Outcome.ok_bind] at h
  match hvA_eq : synthCore n [] a with
  | .outOfFuel => rw [hvA_eq] at h; cases h
  | .error _ => rw [hvA_eq] at h; cases h
  | .ok _vA =>
  rw [hvA_eq] at h; simp only [Outcome.ok_bind] at h
  match haV_eq : evalSubst n SubstEval.unfBound a with
  | .outOfFuel => rw [haV_eq] at h; cases h
  | .error _ => rw [haV_eq] at h; cases h
  | .ok aV =>
  rw [haV_eq] at h; simp only [Outcome.ok_bind] at h
  match hfV_eq : evalSubst n SubstEval.unfBound f with
  | .outOfFuel => rw [hfV_eq] at h; cases h
  | .error _ => rw [hfV_eq] at h; cases h
  | .ok fV =>
  rw [hfV_eq] at h; simp only [Outcome.ok_bind] at h
  -- Build proof ingredients
  have ⟨hfV_f, hf_fV⟩ := evalSubst_equiv hclF hfV_eq
  have ⟨haV_a, ha_aV⟩ := evalSubst_equiv hclA haV_eq
  have hcl_fV := Och.Soundness.evalSubst_closedAt hclF hfV_eq
  have hf_vF := ihF n vF hclF hvF_eq
  -- fV ⊑ vF: chain through f
  have hfV_vF : Subtype' [] [] fV vF := .trans hfV_f hf_vF
  -- Step 1: (.app f a) ⊑ (.app fV aV)
  have step1 : Subtype' [] [] (.app f a) (.app fV aV) :=
    .app_cong hf_fV ha_aV haV_a
  -- Dispatch on whnfPi: primary path (direct exposure) vs secondary (neutralType)
  -- Use `split` to handle the match on whnfPi result within `h`.
  split at h
  · -- Primary path: whnfPi returned some (.lam piDom piBody)
    rename_i piLam piDom piBody hwhnf
    simp only [] at h
    -- Step 2: fV ⊑ (.lam piDom piBody) via whnfPi_sound (Option B)
    have hcl_vF : closedAt 0 vF = true :=
      synthCore_closedAt hclF hvF_eq
    have hfV_pi : Subtype' [] [] fV (.lam piDom piBody) :=
      whnfPi_sound hcl_vF hcl_fV hfV_vF hwhnf
    have step2 : Subtype' [] [] (.app fV aV) (.app (.lam piDom piBody) aV) :=
      .app_cong hfV_pi (.refl _) (.refl _)
    -- Destructure domain check to extract final evalSubst = .ok v
    match hdomChk : subCheckOpen n [] aV piDom with
    | .outOfFuel => rw [hdomChk] at h; cases h
    | .error _ => rw [hdomChk] at h; cases h
    | .ok true =>
      rw [hdomChk] at h; simp only [Outcome.ok_bind] at h
      -- h : evalSubst n unfBound (.app (.lam piDom piBody) aV) = .ok v
      have hcl_piExpr := whnfPi_closedAt hcl_vF hcl_fV hwhnf
      have hcl_aV := Och.Soundness.evalSubst_closedAt hclA haV_eq
      have hcl_pi : closedAt 0 (.app (.lam piDom piBody) aV) = true := by
        simp only [closedAt, Bool.and_eq_true] at hcl_piExpr ⊢
        exact ⟨hcl_piExpr, hcl_aV⟩
      exact .trans step1 (.trans step2 (evalSubst_equiv hcl_pi h).2)
    | .ok false =>
      rw [hdomChk] at h; simp only [Outcome.ok_bind] at h
      -- Domain check failed initially, neutralType fallback for arg
      match hntA : neutralType n [] aV with
      | .ok (some aTy) =>
        rw [hntA] at h; simp only [Outcome.ok_bind] at h
        match hdomChk2 : subCheckOpen n [] aTy piDom with
        | .outOfFuel => rw [hdomChk2] at h; cases h
        | .error _ => rw [hdomChk2] at h; cases h
        | .ok true =>
          rw [hdomChk2] at h; simp only [Outcome.ok_bind] at h
          have hcl_aV' := Och.Soundness.evalSubst_closedAt hclA haV_eq
          have hcl_piExpr' := whnfPi_closedAt hcl_vF hcl_fV hwhnf
          have hcl_pi : closedAt 0 (.app (.lam piDom piBody) aV) = true := by
            simp only [closedAt, Bool.and_eq_true] at hcl_piExpr' ⊢
            exact ⟨hcl_piExpr', hcl_aV'⟩
          exact .trans step1 (.trans step2 (evalSubst_equiv hcl_pi h).2)
        | .ok false =>
          rw [hdomChk2] at h; simp only [Outcome.ok_bind] at h; cases h
      | .ok none =>
        rw [hntA] at h; simp only [Outcome.ok_bind] at h; cases h
      | .outOfFuel => rw [hntA] at h; cases h
      | .error _ => rw [hntA] at h; cases h
  · -- Secondary path: whnfPi didn't directly expose a lam.
    -- Falls through to neutralType on vF, then whnfPi on the result.
    -- Destructure neutralType call
    match hntF : neutralType n [] vF with
    | .outOfFuel => rw [hntF] at h; cases h
    | .error _ => rw [hntF] at h; cases h
    | .ok none => rw [hntF] at h; simp only [Outcome.ok_bind] at h; cases h
    | .ok (some tyF) =>
      rw [hntF] at h; simp only [Outcome.ok_bind] at h
      -- synthNeutralType_to_sub: vF ⊑ tyF
      have hvF_tyF : Subtype' [] [] vF tyF := synthNeutralType_to_sub hntF
      -- fV ⊑ tyF via chain: fV ⊑ f ⊑ vF ⊑ tyF
      have hfV_tyF : Subtype' [] [] fV tyF := .trans hfV_vF hvF_tyF
      -- Destructure second whnfPi call
      split at h
      · -- whnfPi returned some (.lam piDom piBody)
        rename_i piLam piDom piBody hwp2
        simp only [] at h
        -- whnfPi_sound_open: fV ⊑ (.lam piDom piBody)
        have hfV_pi : Subtype' [] [] fV (.lam piDom piBody) :=
          whnfPi_sound_open [] [] hfV_tyF hwp2
        have step2 : Subtype' [] [] (.app fV aV) (.app (.lam piDom piBody) aV) :=
          .app_cong hfV_pi (.refl _) (.refl _)
        -- Destructure domain check
        match hdomChk : subCheckOpen n [] aV piDom with
        | .outOfFuel => rw [hdomChk] at h; cases h
        | .error _ => rw [hdomChk] at h; cases h
        | .ok true =>
          rw [hdomChk] at h; simp only [Outcome.ok_bind] at h
          -- Final eval bridge
          have hcl_vF' : closedAt 0 vF = true := synthCore_closedAt hclF hvF_eq
          have hcl_tyF := neutralType_closedAt hcl_vF' hntF
          have hcl_piExpr := whnfPi_closedAt hcl_tyF hcl_fV hwp2
          have hcl_aV := Och.Soundness.evalSubst_closedAt hclA haV_eq
          have hcl_pi : closedAt 0 (.app (.lam piDom piBody) aV) = true := by
            simp only [closedAt, Bool.and_eq_true] at hcl_piExpr ⊢
            exact ⟨hcl_piExpr, hcl_aV⟩
          exact .trans step1 (.trans step2 (evalSubst_equiv hcl_pi h).2)
        | .ok false =>
          rw [hdomChk] at h; simp only [Outcome.ok_bind] at h
          -- Domain check failed initially, neutralType fallback for arg
          match hntA : neutralType n [] aV with
          | .ok (some aTy) =>
            rw [hntA] at h; simp only [Outcome.ok_bind] at h
            match hdomChk2 : subCheckOpen n [] aTy piDom with
            | .outOfFuel => rw [hdomChk2] at h; cases h
            | .error _ => rw [hdomChk2] at h; cases h
            | .ok true =>
              rw [hdomChk2] at h; simp only [Outcome.ok_bind] at h
              have hcl_vF' := synthCore_closedAt hclF hvF_eq
              have hcl_tyF := neutralType_closedAt hcl_vF' hntF
              have hcl_piExpr := whnfPi_closedAt hcl_tyF hcl_fV hwp2
              have hcl_aV' := Och.Soundness.evalSubst_closedAt hclA haV_eq
              have hcl_pi : closedAt 0 (.app (.lam piDom piBody) aV) = true := by
                simp only [closedAt, Bool.and_eq_true] at hcl_piExpr ⊢
                exact ⟨hcl_piExpr, hcl_aV'⟩
              exact .trans step1 (.trans step2 (evalSubst_equiv hcl_pi h).2)
            | .ok false =>
              rw [hdomChk2] at h; simp only [Outcome.ok_bind] at h; cases h
          | .ok none =>
            rw [hntA] at h; simp only [Outcome.ok_bind] at h; cases h
          | .outOfFuel => rw [hntA] at h; cases h
          | .error _ => rw [hntA] at h; cases h
      · -- whnfPi returned something else; algorithm errors
        simp at h

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
  | app f a ihF _ihA =>
    intro fuel v hcl h
    cases fuel with
    | zero => rw [synthCore.eq_1] at h; cases h
    | succ n =>
      simp only [closedAt, Bool.and_eq_true] at hcl
      exact synthCore_app_WALL hcl.1 hcl.2 h ihF

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
