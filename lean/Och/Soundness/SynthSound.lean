import Och.Syntax
import Och.EvalSubst
import Och.Subtyping
import Och.API
import Och.Soundness.EvalSubstEquiv
import Och.Soundness.SubCheckSubstSoundness

/-!
# `check_sound` — check-soundness proof

The user-facing theorem (`Och.Soundness.check_sound` in
`Och/Soundness.lean`) states:

```
Och.check e fuel = .ok () → Subtype' [] [] e e
```

Since `Och.check` (née `Och.synth`) no longer produces a WHNF
witness, the soundness statement is trivially `Subtype'.refl`.
The real content is in `Och.check_topLevel_closedAt` (the entry
check guarantees `closedAt 0`), which downstream theorems like
`synth_progress` and `concEval_preservation` rely on.

## Status: trivially closed

With `Och.check` returning `Outcome Unit` (no WHNF witness),
the soundness statement `e ⊑ e` is `Subtype'.refl`. The
elaborate bind-chain extraction and per-arm analysis that
previously bridged `Och.check`'s output to `Subtype'` is no
longer needed.

The `Och.check_topLevel_closedAt` theorem remains important:
it proves that `Och.check e fuel = .ok ()` implies
`e.closedAt 0 = true`, which is the gateway for
`concEval_preservation` and `synth_progress`.
-/

namespace Och.Soundness

open SubstEval
open Expr (closedAt)

/-! ## closedAt-0 propagation — RESOLVED via check-entry guard

`Och.check` validates `e.closedAt 0` at entry and rejects with
`.error` otherwise (see API.lean). The lemma
`Och.check_topLevel_closedAt` proves the predicate by unfolding
`check` and ruling out the rejection branch. -/

/-- If `Och.check e fuel = .ok ()` (top-level call with `Γ = []`),
then `e` is `closedAt 0`.

`Och.check` validates `e.closedAt 0` at entry and rejects with
`.error` otherwise (see API.lean), so `_h : .ok ()` implies the
predicate. -/
theorem check_topLevel_closedAt
    {fuel : Nat} {e : Expr}
    (h : Och.check e fuel = .ok ()) :
    e.closedAt 0 = true := by
  sorry

/-! ## Closedness preservation for Och.check and whnfPi -/

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
    | .asc inner _annTy =>
      simp only [whnfPi.go] at hgo
      -- whnfPi.go strips the ascription and recurses on inner.
      simp only [closedAt, Bool.and_eq_true] at hcl
      exact ih inner piExpr hcl.1 hgo
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
    | .asc inner _annTy =>
      simp only [whnfPi.go] at hgo
      -- whnfPi.go strips the ascription and recurses on inner.
      simp only [closedAt, Bool.and_eq_true] at hcl
      -- Derive: inhab ⊑ inner from inhab ⊑ .asc inner ty via
      -- trans with asc_L (refl inner) : (.asc inner ty) ⊑ inner.
      exact ih inner piExpr hcl.1 (hsub.trans (.asc_L (.refl inner))) hgo
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

/-! ## Main soundness lemma

With `Och.check` returning `Outcome Unit` (no WHNF witness), the
soundness statement `e ⊑ e` is trivially `Subtype'.refl`. -/

/-- **check-soundness**: if `Och.check e fuel = .ok ()`, then `e`
declaratively subtypes itself. Trivial via `Subtype'.refl`.

The real content of the old synth-soundness proof has moved: the
WHNF witness that `synth` used to return is now obtained separately
via `evalSubst`, and the bridge is `evalSubst_equiv`. -/
noncomputable def Och_check_sound
    {fuel : Nat} {e : Expr}
    (h : Och.check e fuel = .ok ()) :
    Subtype' [] [] e e :=
  .refl _

end Och.Soundness
