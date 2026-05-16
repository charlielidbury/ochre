import Och.Subtyping
import Och.EvalSubst
import Och.API
import Och.Soundness.EvalSubstLemmas
import Och.Soundness.CloseAll
import Och.Soundness.SubCheckSubstNeutral
import Och.Soundness.SubCheckSubstStructural
import Och.Soundness.SubCheckSubstFallback

/-!
# `subCheckSubst_sound` — the main soundness theorem

With intrinsic typing, the algorithm `subCheckSubst` now returns
`Outcome (Subtype' S Γ a b)` — the derivation IS the payload on
success. Soundness is trivial: extract the derivation from `.ok`.

## Key results retained

- `evalSubst_equiv_open`: eval bridge for open terms (used by SynthSound)
- `whnfPi_go_sound_open`, `whnfPi_sound_open`: Pi-exposure soundness
- `synthNeutralType_to_sub`: synth soundness for neutrals
- `subCheckSubst_sound`: top-level soundness (now trivial)
- `Och_subCheck_sound`: surface-level bridge

## Deprecated internal proofs

The per-arm soundness lemmas (`subCheckSubstMatch_sound_gen`,
`subCheckSpine_sound`, `neutralAscent_sound`, etc.) are no longer
needed since the algorithm constructs derivations intrinsically.
They have been removed.
-/

namespace Och.Soundness

open SubstEval

/-! ## Eval bridge for open terms

Generalizes `evalSubst_equiv` to arbitrary `S, Γ` with no closedness
precondition. The proof is by induction on fuel, identical to
`evalSubst_equiv` but with `Subtype'.refl` at the `bvar` case
instead of a vacuous truth. -/

/-- `evalSubst` preserves subtype equivalence at arbitrary `S, Γ`. -/
noncomputable def evalSubst_equiv_open
    {fuel unf : Nat} {e e' : Expr} (S : Seen) (Γ : Ctx)
    (hstep : evalSubst fuel unf e = .ok e') :
    Subtype' S Γ e' e × Subtype' S Γ e e' := by
  induction fuel generalizing unf e e' with
  | zero => rw [evalSubst.eq_1] at hstep; cases hstep
  | succ n ih =>
    match e, hstep with
    | .bvar k, h =>
      rw [evalSubst.eq_2] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .type, h =>
      rw [evalSubst.eq_3] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .bot, h =>
      rw [evalSubst.eq_4] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .lam dom body, h =>
      rw [evalSubst.eq_5] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .iota ann body, h =>
      rw [evalSubst.eq_6] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .fix ann body, h =>
      rw [evalSubst.eq_7] at h
      simp only [Outcome.ok.injEq] at h; subst h
      exact ⟨.refl _, .refl _⟩
    | .asc t ty, h =>
      rw [evalSubst.eq_8] at h
      match ht : evalSubst n unf t with
      | .outOfFuel => rw [ht] at h; cases h
      | .error _ => rw [ht] at h; cases h
      | .ok tv =>
        match hty : evalSubst n unf ty with
        | .outOfFuel => rw [ht, hty] at h; simp only [Outcome.ok_bind] at h; cases h
        | .error _ => rw [ht, hty] at h; simp only [Outcome.ok_bind] at h; cases h
        | .ok tyv =>
          rw [ht, hty] at h
          simp only [Outcome.ok_bind, Outcome.ok.injEq] at h; subst h
          have ⟨ht₁, ht₂⟩ := ih ht
          refine ⟨?_, ?_⟩
          · exact .asc_L (.asc_R ht₁)
          · exact .asc_L (.asc_R ht₂)
    | .letE val body, h =>
      rw [evalSubst.eq_9] at h
      match hvEv : evalSubst n unf val with
      | .outOfFuel => rw [hvEv] at h; cases h
      | .error _ => rw [hvEv] at h; cases h
      | .ok vv =>
        simp only [hvEv] at h
        have ⟨hvv₁, hvv₂⟩ := ih hvEv
        simp only [Outcome.ok_bind] at h
        have ⟨he₁, he₂⟩ := ih h
        refine ⟨?_, ?_⟩
        · exact .trans he₁ (.trans (.letE_R (.refl _)) (.letE_cong hvv₁ (.refl _)))
        · exact .trans (.letE_cong hvv₂ (.refl _)) (.trans (.letE_L (.refl _)) he₂)
    | .app f a, h =>
      rw [evalSubst.eq_10] at h
      match hfEv : evalSubst n unf f with
      | .outOfFuel => rw [hfEv] at h; cases h
      | .error _ => rw [hfEv] at h; cases h
      | .ok fv =>
        have ⟨hf₁, hf₂⟩ := ih hfEv
        match haEv : evalSubst n unf a with
        | .outOfFuel => rw [hfEv, haEv] at h; cases h
        | .error _ => rw [hfEv, haEv] at h; cases h
        | .ok av =>
          have ⟨ha₁, ha₂⟩ := ih haEv
          rw [hfEv, haEv] at h
          simp only [Outcome.ok_bind] at h
          cases fv with
          | bvar _ =>
            simp only at h; simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | type =>
            simp only at h; simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | bot =>
            simp only at h; simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | lam dom body =>
            simp only at h
            have ⟨he₁, he₂⟩ := ih h
            exact ⟨.trans he₁ (.trans (.beta_R (.refl _)) (.app_cong hf₁ ha₁ ha₂)),
              .trans (.app_cong hf₂ ha₂ ha₁) (.trans (.beta_L (.refl _)) he₂)⟩
          | iota ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h; subst h
              exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
            · have ⟨he₁, he₂⟩ := ih h
              exact ⟨.trans he₁ (.trans (.app_cong (.unfold_iota_R (.refl _)) (.refl _) (.refl _))
                  (.app_cong hf₁ ha₁ ha₂)),
                .trans (.app_cong hf₂ ha₂ ha₁)
                  (.trans (.app_cong (.unfold_iota_L (.refl _)) (.refl _) (.refl _)) he₂)⟩
          | fix ann body =>
            simp only at h
            split at h
            · simp only [Outcome.ok.injEq] at h; subst h
              exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
            · have ⟨he₁, he₂⟩ := ih h
              exact ⟨.trans he₁ (.trans (.app_cong (.unfold_fix_R (.refl _)) (.refl _) (.refl _))
                  (.app_cong hf₁ ha₁ ha₂)),
                .trans (.app_cong hf₂ ha₂ ha₁)
                  (.trans (.app_cong (.unfold_fix_L (.refl _)) (.refl _) (.refl _)) he₂)⟩
          | asc inner _ =>
            simp only at h
            have ⟨he₁, he₂⟩ := ih h
            exact ⟨.trans he₁ (.app_cong (.trans (.asc_R (.refl _)) hf₁) ha₁ ha₂),
              .trans (.app_cong (.trans hf₂ (.asc_L (.refl _))) ha₂ ha₁) he₂⟩
          | letE vv b =>
            simp only at h; simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩
          | app f' a' =>
            simp only at h; simp only [Outcome.ok.injEq] at h; subst h
            exact ⟨.app_cong hf₁ ha₁ ha₂, .app_cong hf₂ ha₂ ha₁⟩

/-! ## Open-context whnfPi soundness

`whnfPi_go_sound_open` and `whnfPi_sound_open` generalise the
closed-context `whnfPi_go_sound` / `whnfPi_sound` (in SynthSound.lean)
to arbitrary `S, Γ` with no `closedAt 0` precondition. The proof
strategy is identical (Option B: track `inhab ⊑ e` through the loop)
but uses `evalSubst_equiv_open` instead of the closed `evalSubst_equiv`. -/

/-- Open-context inner loop soundness: if `go n e = some piExpr` and
`Subtype' S Γ inhab e`, then `Subtype' S Γ inhab piExpr`. -/
noncomputable def whnfPi_go_sound_open
    (fuel : Nat) (inhab : Expr) (S : Seen) (Γ : Ctx)
    : ∀ (n : Nat) (e piExpr : Expr),
      Subtype' S Γ inhab e →
      whnfPi.go fuel inhab n e = some piExpr →
      Subtype' S Γ inhab piExpr := by
  intro n
  induction n with
  | zero =>
    intro e piExpr hsub hgo
    simp only [whnfPi.go] at hgo
    injection hgo with hgo; subst hgo; exact hsub
  | succ m ih =>
    intro e piExpr hsub hgo
    match e with
    | .lam dom body =>
      simp only [whnfPi.go] at hgo
      injection hgo with hgo; subst hgo; exact hsub
    | .fix ann body =>
      simp only [whnfPi.go] at hgo
      match hev : evalSubst fuel 4 (body.subst 0 (.fix ann body)) with
      | .ok e' =>
        rw [hev] at hgo
        have ⟨_, hfwd⟩ := evalSubst_equiv_open S Γ hev
        have step_unfold : Subtype' S Γ (.fix ann body)
            (body.subst 0 (.fix ann body)) :=
          .unfold_fix_L (.refl _)
        have hsub' : Subtype' S Γ inhab e' :=
          .trans hsub (.trans step_unfold hfwd)
        exact ih e' piExpr hsub' hgo
      | .outOfFuel => rw [hev] at hgo; cases hgo
      | .error _ => rw [hev] at hgo; cases hgo
    | .iota _ann _body =>
      simp only [whnfPi.go] at hgo
      match hev : evalSubst fuel 4 (_body.subst 0 inhab) with
      | .ok e' =>
        rw [hev] at hgo
        have ⟨_, hfwd⟩ := evalSubst_equiv_open S Γ hev
        have step_elim : Subtype' S Γ inhab (_body.subst 0 inhab) :=
          .iota_elim hsub
        have hsub' : Subtype' S Γ inhab e' :=
          .trans step_elim hfwd
        exact ih e' piExpr hsub' hgo
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

/-- Open-context `whnfPi` soundness: if `whnfPi fuel inhab ty = some piExpr`
and `Subtype' S Γ inhab ty`, then `Subtype' S Γ inhab piExpr`.
No closedness precondition. -/
noncomputable def whnfPi_sound_open
    {fuel : Nat} {inhab ty piExpr : Expr} (S : Seen) (Γ : Ctx)
    (hsub_inhab : Subtype' S Γ inhab ty)
    (h : whnfPi fuel inhab ty = some piExpr) :
    Subtype' S Γ inhab piExpr := by
  unfold whnfPi at h
  match hev : evalSubst fuel SubstEval.unfBound ty with
  | .ok ty' =>
    rw [hev] at h
    have ⟨_, hfwd⟩ := evalSubst_equiv_open S Γ hev
    exact whnfPi_go_sound_open fuel inhab S Γ
      SubstEval.unfBound ty' piExpr (.trans hsub_inhab hfwd) h
  | .outOfFuel => rw [hev] at h; cases h
  | .error _ => rw [hev] at h; cases h

/-! ### synthNeutralType soundness (general)

Full soundness of `synthNeutralType`: if it returns `some ty` for
neutral `a`, then `Subtype' S Γ a ty`. The proof inducts on fuel `n`
so the `.app` case can apply the IH at `n-1` for the recursive call
on the function head. -/

/-- When `synthNeutralType` succeeds on `.bvar k`, produce a
    `Subtype'.bvar` derivation directly. -/
private noncomputable def synthNeutralType_bvar_to_sub
    {n : Nat} {Γ : Ctx} {k : Nat} {ty : Expr} {S : Seen}
    (h : synthNeutralType n Γ (.bvar k) = .ok (some ty)) :
    Subtype' S Γ (.bvar k) ty := by
  cases n with
  | zero => rw [synthNeutralType.eq_def] at h; cases h
  | succ m =>
    rw [synthNeutralType.eq_def] at h; simp only [] at h
    match hget : Γ.get? k with
    | none => rw [hget] at h; simp at h
    | some τ =>
      rw [hget] at h; simp only [Outcome.ok.injEq, Option.some.injEq] at h
      rw [← h]
      exact .bvar hget

/-- If `synthNeutralType` returns `some ty` for a neutral `a`, then
    `Subtype' S Γ a ty`. -/
noncomputable def synthNeutralType_to_sub
    {n : Nat} {Γ : Ctx} {a ty : Expr} {S : Seen}
    (h : synthNeutralType n Γ a = .ok (some ty)) :
    Subtype' S Γ a ty := by
  induction n generalizing a ty with
  | zero => rw [synthNeutralType.eq_def] at h; cases h
  | succ m ih =>
    cases a with
    | bvar k => exact synthNeutralType_bvar_to_sub h
    | app f arg =>
      rw [synthNeutralType.eq_def] at h; simp only [] at h
      -- Destructure: synthNeutralType m Γ f
      match hnt : synthNeutralType m Γ f with
      | .outOfFuel => rw [hnt] at h; cases h
      | .error _ => rw [hnt] at h; cases h
      | .ok none => rw [hnt] at h; simp only [Outcome.ok_bind] at h; cases h
      | .ok (some fTy) =>
        rw [hnt] at h; simp only [Outcome.ok_bind] at h
        -- IH: f ⊑ fTy
        have hf_sub : Subtype' S Γ f fTy := ih hnt
        -- Rewrite exposePi to whnfPi
        rw [exposePi_eq_whnfPi] at h
        split at h
        · -- whnfPi returned some (.lam dom retTy)
          rename_i dom retTy hwp
          -- whnfPi_sound_open: f ⊑ (.lam dom retTy)
          have hf_pi : Subtype' S Γ f (.lam dom retTy) :=
            whnfPi_sound_open S Γ hf_sub hwp
          -- Now h is about the evalSubst step
          match hev : evalSubst (m + 1) unfBound (retTy.subst 0 arg) with
          | .ok r =>
            rw [hev] at h
            simp only [Outcome.ok.injEq, Option.some.injEq] at h
            subst h
            -- app_elim: (.app f arg) ⊑ (retTy.subst 0 arg)
            have happ : Subtype' S Γ (.app f arg) (retTy.subst 0 arg) :=
              .app_elim hf_pi
            -- eval bridge: (retTy.subst 0 arg) ⊑ r
            have ⟨_, hfwd⟩ := evalSubst_equiv_open S Γ hev
            exact .trans happ hfwd
          | .outOfFuel => rw [hev] at h; simp at h
          | .error _ => rw [hev] at h; simp at h
        · -- whnfPi returned something else
          simp at h
    | fix ann body =>
      rw [synthNeutralType.eq_def] at h; simp only [] at h
      match hev : evalSubst (m + 1) unfBound ann with
      | .ok ann' =>
        rw [hev] at h
        simp only [Outcome.ok.injEq, Option.some.injEq] at h
        subst h
        have ⟨_, hfwd⟩ := evalSubst_equiv_open S Γ hev
        exact .trans .fix_ann hfwd
      | .outOfFuel => rw [hev] at h; simp at h
      | .error _ => rw [hev] at h; simp at h
    | _ =>
      rw [synthNeutralType.eq_def] at h; simp at h

/-! ## Top-level soundness theorems

With intrinsic typing, soundness is trivial: the algorithm returns
the derivation directly when it succeeds. -/

/-- The main soundness theorem for the structural subtype checker.
    With intrinsic typing, the algorithm returns the derivation as
    its payload — soundness is extraction. -/
noncomputable def subCheckSubst_sound
    {fuel : Nat} {a b : Expr}
    (h : SubstEval.subCheck fuel a b = .ok true) :
    Subtype' [] [] a b := by
  simp only [SubstEval.subCheck] at h
  match hsub : SubstEval.subCheckSubst fuel [] [] a b with
  | .ok deriv =>
    exact deriv
  | .outOfFuel =>
    rw [hsub] at h; cases h
  | .error _ =>
    rw [hsub] at h; cases h

/-- Surface-level soundness: `Och.subCheck a b fuel = .ok true →
    Subtype' [] [] a.whnf b.whnf`. -/
noncomputable def Och_subCheck_sound
    {a b : Och.WTValue} {fuel : Nat}
    (h : Och.subCheck a b fuel = .ok true) :
    Subtype' [] [] a.whnf b.whnf := by
  -- Och.subCheck unfolds to SubstEval.subCheck
  simp only [Och.subCheck, SubstEval.subCheck] at h
  exact subCheckSubst_sound h

end Och.Soundness
