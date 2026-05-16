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

Assembles the per-arm lemmas into the engine-level soundness theorem:

```
subCheck fuel a b = .ok true → Subtype' [] [] a b
```

## Proof structure

By induction on `fuel`:
- `subCheckSubst (n+1)` evaluates both sides, strips ascriptions,
  checks fast paths, delegates to `subCheckSubstMatch n`.
- `subCheckSubstMatch n` calls `subCheckSubst n` recursively.
- The eval bridge (`evalSubst_equiv_open`) connects inputs to WHNF.

## Sorry inventory (this file)

- `subCheckSubst_sound_gen` fuel-inductive step: sorry'd due to
  match-unfolding difficulties with the mutual def's equation lemma.
  The proof obligation is clear (see comments) and each sub-case
  independently closable.
- `subCheckSubstMatch_sound_gen` arms:
  - `lam, lam`: CLOSED
  - `bot, _`: CLOSED
  - All other arms: sorry'd (iota-iota, fix-fix, fallbacks, neutral)
- `seen_hit` in `subCheckSubst_sound_gen`: needs depth-tag + shift invariant
- `Och_subCheck_sound`: sorry'd (depends on API-level bridge)

## Closed results

- `evalSubst_equiv_open`: eval bridge for open terms (no sorry)
- `stripAscL_super`, `stripAscR_sub`: ascription stripping bridge (no sorry)
- `subCheckSubst_sound`: top-level composition (no sorry except in callees)
- `subCheckSubstMatch_sound_gen` lam-lam arm (no sorry)
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

/-! ## Ascription stripping bridge -/

/-- LHS asc strip: `a' ⊑ stripAscL a'`. -/
private noncomputable def stripAscL_super (S : Seen) (Γ : Ctx) (a' : Expr) :
    Subtype' S Γ a' (match a' with | .asc _ ty => ty | x => x) :=
  match a' with
  | .asc _ _ => .asc_L_ann (.refl _)
  | .bvar _ | .lam _ _ | .app _ _ | .type | .bot | .iota _ _ | .fix _ _ | .letE _ _ => .refl _

/-- RHS asc strip: `stripAscR b' ⊑ b'`. -/
private noncomputable def stripAscR_sub (S : Seen) (Γ : Ctx) (b' : Expr) :
    Subtype' S Γ (match b' with | .asc e _ => e | x => x) b' :=
  match b' with
  | .asc _ _ => .asc_R (.refl _)
  | .bvar _ | .lam _ _ | .app _ _ | .type | .bot | .iota _ _ | .fix _ _ | .letE _ _ => .refl _

/-! ## Common arm helpers -/

/-! ## Soundness for `subCheckSubstMatch`

Given the IH for `subCheckSubst` at fuel `n`, prove each arm of
`subCheckSubstMatch n` is sound. -/

private noncomputable def subCheckSubstMatch_sound_gen
    (n : Nat)
    (ih_sub : ∀ (Γ' : Ctx) (S' : Seen) (a' b' : Expr),
      subCheckSubst n Γ' S' a' b' = .ok true → Subtype' S' Γ' a' b')
    (Γ : Ctx) (S : Seen) (a b : Expr)
    (h : subCheckSubstMatch n Γ S a b = .ok true) :
    Subtype' S Γ a b := by
  cases a with
  | bot => exact .bot_L
  | lam domA bodyA =>
    cases b with
    | lam domB bodyB =>
      unfold subCheckSubstMatch at h
      match hc : subCheckSubst n Γ S domB domA with
      | .outOfFuel => rw [hc] at h; cases h
      | .error _ => rw [hc] at h; cases h
      | .ok contra_r =>
        rw [hc] at h; simp only [Outcome.ok_bind] at h
        match contra_r with
        | false => simp at h
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false, Outcome.ok_bind] at h
          exact .lam (ih_sub _ _ _ _ hc) (ih_sub _ _ _ _ h)
    | bvar _ => unfold subCheckSubstMatch at h; simp [isNeutral] at h
    | app _ _ => unfold subCheckSubstMatch at h; simp [isNeutral] at h
    | type => unfold subCheckSubstMatch at h; simp [isNeutral] at h
    | bot => unfold subCheckSubstMatch at h; simp [isNeutral] at h
    | asc _ _ => unfold subCheckSubstMatch at h; simp [isNeutral] at h
    | letE _ _ => unfold subCheckSubstMatch at h; simp [isNeutral] at h
    | iota annB bodyB =>
      -- lam, iota: falls through to (_, .iota) arm = iotaIntro
      unfold subCheckSubstMatch at h; simp only [Outcome.ok_bind] at h
      match hann : subCheckSubst n Γ ((Γ.length, Expr.lam domA bodyA, Expr.iota annB bodyB) :: S) (Expr.lam domA bodyA) annB with
      | .outOfFuel => rw [hann] at h; cases h
      | .error _ => rw [hann] at h; cases h
      | .ok annOk =>
        rw [hann] at h; simp only [Outcome.ok_bind] at h
        match annOk with
        | false => simp at h
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
          match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.lam domA bodyA)) with
          | .outOfFuel => rw [hev] at h; simp at h
          | .error _ => rw [hev] at h; simp at h
          | .ok bodyB'' =>
            rw [hev] at h; simp only [] at h
            have ⟨hev_sub, _⟩ := evalSubst_equiv_open
              ((Γ.length, Expr.lam domA bodyA, Expr.iota annB bodyB) :: S) Γ hev
            exact .iota_intro (ih_sub _ _ _ _ hann)
              (.trans (ih_sub _ _ _ _ h) hev_sub)
    | fix annB bodyB =>
      -- lam, fix: falls through to (_, .fix) arm = unfoldFixR
      unfold subCheckSubstMatch at h; simp only [isNeutral, Outcome.ok_bind] at h
      match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.fix annB bodyB)) with
      | .outOfFuel => rw [hev] at h; simp at h
      | .error _ => rw [hev] at h; simp at h
      | .ok b' =>
        rw [hev] at h; simp only [] at h
        have ⟨hev_sub, _⟩ := evalSubst_equiv_open
          ((Γ.length, Expr.lam domA bodyA, Expr.fix annB bodyB) :: S) Γ hev
        exact .unfold_fix_R (.trans (ih_sub _ _ _ _ h) hev_sub)
  | iota annA bodyA =>
    cases b with
    | iota annB bodyB =>
      -- iota, iota: structural try, fallback to iotaIntro
      unfold subCheckSubstMatch at h
      -- The algorithm tries structural first, then falls back.
      -- Case-split on the structural result.
      simp only [Outcome.ok_bind] at h
      -- The structural result is: subCheckSubst n Γ S annA annB >>= ...
      -- After match, if .ok true => done, else fallback to iotaIntro
      -- Let's generalize the structural computation
      match hstr : (do
          let annOk ← subCheckSubst n Γ S annA annB
          if !annOk then return false
          subCheckSubst n (annB :: Γ) S bodyA bodyB : Outcome Bool) with
      | .ok true =>
        -- Structural path succeeded
        rw [hstr] at h
        simp only [Outcome.ok_bind] at hstr
        match hann : subCheckSubst n Γ S annA annB with
        | .outOfFuel => rw [hann] at hstr; cases hstr
        | .error _ => rw [hann] at hstr; cases hstr
        | .ok annOk =>
          rw [hann] at hstr; simp only [Outcome.ok_bind] at hstr
          match annOk with
          | false => simp at hstr
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ite_false, Outcome.ok_bind] at hstr
            exact .iota_cong (ih_sub _ _ _ _ hann) (ih_sub _ _ _ _ hstr)
      | .ok false =>
        rw [hstr] at h; simp only [Outcome.ok_bind] at h
        -- Fallback to iotaIntro
        match hann : subCheckSubst n Γ ((Γ.length, Expr.iota annA bodyA, Expr.iota annB bodyB) :: S) (Expr.iota annA bodyA) annB with
        | .outOfFuel => rw [hann] at h; cases h
        | .error _ => rw [hann] at h; cases h
        | .ok annOk2 =>
          rw [hann] at h; simp only [Outcome.ok_bind] at h
          match annOk2 with
          | false => simp at h
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
            match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.iota annA bodyA)) with
            | .outOfFuel => rw [hev] at h; simp at h
            | .error _ => rw [hev] at h; simp at h
            | .ok bodyB'' =>
              rw [hev] at h; simp only [] at h
              have hsub := ih_sub _ _ _ _ h
              refine .iota_intro (ih_sub _ _ _ _ hann) ?_
              exact hsub.trans (evalSubst_equiv_open _ Γ hev).1
      | .outOfFuel =>
        rw [hstr] at h; simp only [Outcome.ok_bind] at h
        -- Same fallback as .ok false
        match hann : subCheckSubst n Γ ((Γ.length, Expr.iota annA bodyA, Expr.iota annB bodyB) :: S) (Expr.iota annA bodyA) annB with
        | .outOfFuel => rw [hann] at h; cases h
        | .error _ => rw [hann] at h; cases h
        | .ok annOk2 =>
          rw [hann] at h; simp only [Outcome.ok_bind] at h
          match annOk2 with
          | false => simp at h
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
            match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.iota annA bodyA)) with
            | .outOfFuel => rw [hev] at h; simp at h
            | .error _ => rw [hev] at h; simp at h
            | .ok bodyB'' =>
              rw [hev] at h; simp only [] at h
              have hsub := ih_sub _ _ _ _ h
              refine .iota_intro (ih_sub _ _ _ _ hann) ?_
              exact hsub.trans (evalSubst_equiv_open _ Γ hev).1
      | .error _ =>
        rw [hstr] at h; simp only [Outcome.ok_bind] at h
        match hann : subCheckSubst n Γ ((Γ.length, Expr.iota annA bodyA, Expr.iota annB bodyB) :: S) (Expr.iota annA bodyA) annB with
        | .outOfFuel => rw [hann] at h; cases h
        | .error _ => rw [hann] at h; cases h
        | .ok annOk2 =>
          rw [hann] at h; simp only [Outcome.ok_bind] at h
          match annOk2 with
          | false => simp at h
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
            match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.iota annA bodyA)) with
            | .outOfFuel => rw [hev] at h; simp at h
            | .error _ => rw [hev] at h; simp at h
            | .ok bodyB'' =>
              rw [hev] at h; simp only [] at h
              have hsub := ih_sub _ _ _ _ h
              refine .iota_intro (ih_sub _ _ _ _ hann) ?_
              exact hsub.trans (evalSubst_equiv_open _ Γ hev).1
    | fix annB bodyB =>
      -- iota, fix: falls through to (_, .fix) arm
      -- Actually looking at match order: (.iota, .iota) doesn't match,
      -- (.iota, .fix) is NOT (_, .iota) since b=.fix, NOT (.fix, _) since a=.iota,
      -- NOT (.iota, _) either because the (.iota, _) arm comes AFTER (_, .fix).
      -- Wait, let me re-check the match order:
      -- .bot, _ -> ok
      -- .lam, .lam -> structural
      -- .iota, .iota -> structural+fallback
      -- .fix, .fix -> structural+fallback
      -- _, .iota -> iotaIntro     <-- catches (.fix, .iota) but NOT (.iota, .fix)
      -- _, .fix -> unfoldFixR     <-- catches (.iota, .fix)
      -- .fix, _ -> unfoldFixL
      -- .iota, _ -> unfoldIotaL
      -- _, _ -> neutral
      -- So (.iota, .fix) hits the (_, .fix) arm = unfoldFixR
      unfold subCheckSubstMatch at h
      -- isNeutral (.iota ..) = false, so straight to unfoldFixR
      simp only [isNeutral, Outcome.ok_bind] at h
      match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.fix annB bodyB)) with
      | .outOfFuel => rw [hev] at h; simp at h
      | .error _ => rw [hev] at h; simp at h
      | .ok b' =>
        rw [hev] at h; simp only [] at h
        have hsub := ih_sub _ _ _ _ h
        refine .unfold_fix_R ?_
        exact hsub.trans (evalSubst_equiv_open _ Γ hev).1
    | bvar _ | lam _ _ | app _ _ | type | bot | asc _ _ | letE _ _ =>
      -- iota, other: (.iota, _) = unfoldIotaL
      all_goals (
        unfold subCheckSubstMatch at h; simp only [Outcome.ok_bind] at h
        match hev : evalSubst (n + 1) unfBound (bodyA.subst 0 (Expr.iota annA bodyA)) with
        | .outOfFuel => rw [hev] at h; simp at h
        | .error _ => rw [hev] at h; simp at h
        | .ok a' =>
          rw [hev] at h; simp only [] at h
          by_cases heqa : a' == Expr.iota annA bodyA
          · simp [heqa] at h
          · simp only [heqa, ite_false] at h
            -- ih_sub gives Subtype' seen' Γ a' b where seen' includes b
            have hsub := ih_sub _ _ _ _ h
            -- Apply unfold_iota_L; the premise is:
            -- Subtype' seen' Γ (bodyA.subst 0 (iota annA bodyA)) b
            -- We get this from eval bridge (at any S) + ih_sub
            refine .unfold_iota_L ?_
            exact .trans (evalSubst_equiv_open _ Γ hev).2 hsub)
  | fix annA bodyA =>
    cases b with
    | iota annB bodyB =>
      -- fix, iota: (_, .iota) = iotaIntro
      unfold subCheckSubstMatch at h; simp only [Outcome.ok_bind] at h
      match hann : subCheckSubst n Γ ((Γ.length, Expr.fix annA bodyA, Expr.iota annB bodyB) :: S) (Expr.fix annA bodyA) annB with
      | .outOfFuel => rw [hann] at h; cases h
      | .error _ => rw [hann] at h; cases h
      | .ok annOk =>
        rw [hann] at h; simp only [Outcome.ok_bind] at h
        match annOk with
        | false => simp at h
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
          match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.fix annA bodyA)) with
          | .outOfFuel => rw [hev] at h; simp at h
          | .error _ => rw [hev] at h; simp at h
          | .ok bodyB'' =>
            rw [hev] at h; simp only [] at h
            have ⟨hev_sub, _⟩ := evalSubst_equiv_open
              ((Γ.length, Expr.fix annA bodyA, Expr.iota annB bodyB) :: S) Γ hev
            exact .iota_intro (ih_sub _ _ _ _ hann)
              (.trans (ih_sub _ _ _ _ h) hev_sub)
    | fix annB bodyB =>
      -- fix, fix: structural try, fallback to unfoldFixR
      unfold subCheckSubstMatch at h
      simp only [Outcome.ok_bind] at h
      match hstr : (do
          let annOk ← subCheckSubst n Γ S annA annB
          if !annOk then return false
          subCheckSubst n (annB :: Γ) S bodyA bodyB : Outcome Bool) with
      | .ok true =>
        rw [hstr] at h
        simp only [Outcome.ok_bind] at hstr
        match hann : subCheckSubst n Γ S annA annB with
        | .outOfFuel => rw [hann] at hstr; cases hstr
        | .error _ => rw [hann] at hstr; cases hstr
        | .ok annOk =>
          rw [hann] at hstr; simp only [Outcome.ok_bind] at hstr
          match annOk with
          | false => simp at hstr
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ite_false, Outcome.ok_bind] at hstr
            exact .fix_cong (ih_sub _ _ _ _ hann) (ih_sub _ _ _ _ hstr)
      | .ok false | .outOfFuel | .error _ =>
        rw [hstr] at h; simp only [Outcome.ok_bind] at h
        -- Fallback to unfold_fix_R
        match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.fix annB bodyB)) with
        | .outOfFuel => rw [hev] at h; simp at h
        | .error _ => rw [hev] at h; simp at h
        | .ok b' =>
          rw [hev] at h; simp only [] at h
          have hsub := ih_sub _ _ _ _ h
          refine .unfold_fix_R ?_
          exact hsub.trans (evalSubst_equiv_open _ Γ hev).1
    | bvar _ | lam _ _ | app _ _ | type | bot | asc _ _ | letE _ _ =>
      -- fix, other: (.fix, _) = unfoldFixL
      all_goals (
        unfold subCheckSubstMatch at h; simp only [Outcome.ok_bind] at h
        match hev : evalSubst (n + 1) unfBound (bodyA.subst 0 (Expr.fix annA bodyA)) with
        | .outOfFuel => rw [hev] at h; simp at h
        | .error _ => rw [hev] at h; simp at h
        | .ok a' =>
          rw [hev] at h; simp only [] at h
          by_cases heqa : a' == Expr.fix annA bodyA
          · simp [heqa] at h
          · simp only [heqa, ite_false] at h
            have hsub := ih_sub _ _ _ _ h
            refine .unfold_fix_L ?_
            exact .trans (evalSubst_equiv_open _ Γ hev).2 hsub)
  | bvar k =>
    cases b with
    | iota annB bodyB =>
      -- bvar, iota: (_, .iota) = iotaIntro
      unfold subCheckSubstMatch at h; simp only [Outcome.ok_bind] at h
      match hann : subCheckSubst n Γ ((Γ.length, Expr.bvar k, Expr.iota annB bodyB) :: S) (Expr.bvar k) annB with
      | .outOfFuel => rw [hann] at h; cases h
      | .error _ => rw [hann] at h; cases h
      | .ok annOk =>
        rw [hann] at h; simp only [Outcome.ok_bind] at h
        match annOk with
        | false => simp at h
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
          match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.bvar k)) with
          | .outOfFuel => rw [hev] at h; simp at h
          | .error _ => rw [hev] at h; simp at h
          | .ok bodyB'' =>
            rw [hev] at h; simp only [] at h
            have ⟨hev_sub, _⟩ := evalSubst_equiv_open
              ((Γ.length, Expr.bvar k, Expr.iota annB bodyB) :: S) Γ hev
            exact .iota_intro (ih_sub _ _ _ _ hann)
              (.trans (ih_sub _ _ _ _ h) hev_sub)
    | fix annB bodyB =>
      -- bvar, fix: (_, .fix) arm — sorry (complex neutral check)
      sorry
    | _ =>
      -- bvar, other: (_, _) wildcard = neutral arm
      -- Sorry'd: needs spine compare + neutralAscent soundness
      sorry
  | app f arg =>
    cases b with
    | iota annB bodyB =>
      -- app, iota: (_, .iota) = iotaIntro
      unfold subCheckSubstMatch at h; simp only [Outcome.ok_bind] at h
      match hann : subCheckSubst n Γ ((Γ.length, Expr.app f arg, Expr.iota annB bodyB) :: S) (Expr.app f arg) annB with
      | .outOfFuel => rw [hann] at h; cases h
      | .error _ => rw [hann] at h; cases h
      | .ok annOk =>
        rw [hann] at h; simp only [Outcome.ok_bind] at h
        match annOk with
        | false => simp at h
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
          match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.app f arg)) with
          | .outOfFuel => rw [hev] at h; simp at h
          | .error _ => rw [hev] at h; simp at h
          | .ok bodyB'' =>
            rw [hev] at h; simp only [] at h
            have ⟨hev_sub, _⟩ := evalSubst_equiv_open
              ((Γ.length, Expr.app f arg, Expr.iota annB bodyB) :: S) Γ hev
            exact .iota_intro (ih_sub _ _ _ _ hann)
              (.trans (ih_sub _ _ _ _ h) hev_sub)
    | fix annB bodyB =>
      -- app, fix: (_, .fix) arm — sorry (complex neutral check)
      sorry
    | _ =>
      -- app, other: (_, _) wildcard = neutral arm
      -- Sorry'd: needs spine compare + neutralAscent soundness
      sorry
  | type =>
    cases b with
    | iota annB bodyB =>
      -- type, iota: (_, .iota) = iotaIntro
      unfold subCheckSubstMatch at h; simp only [Outcome.ok_bind] at h
      match hann : subCheckSubst n Γ ((Γ.length, Expr.type, Expr.iota annB bodyB) :: S) Expr.type annB with
      | .outOfFuel => rw [hann] at h; cases h
      | .error _ => rw [hann] at h; cases h
      | .ok annOk =>
        rw [hann] at h; simp only [Outcome.ok_bind] at h
        match annOk with
        | false => simp at h
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
          match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 Expr.type) with
          | .outOfFuel => rw [hev] at h; simp at h
          | .error _ => rw [hev] at h; simp at h
          | .ok bodyB'' =>
            rw [hev] at h; simp only [] at h
            have ⟨hev_sub, _⟩ := evalSubst_equiv_open
              ((Γ.length, Expr.type, Expr.iota annB bodyB) :: S) Γ hev
            exact .iota_intro (ih_sub _ _ _ _ hann)
              (.trans (ih_sub _ _ _ _ h) hev_sub)
    | fix annB bodyB =>
      -- type, fix: (_, .fix) arm
      unfold subCheckSubstMatch at h; simp only [isNeutral, Outcome.ok_bind] at h
      match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.fix annB bodyB)) with
      | .outOfFuel => rw [hev] at h; simp at h
      | .error _ => rw [hev] at h; simp at h
      | .ok b' =>
        rw [hev] at h; simp only [] at h
        have ⟨hev_sub, _⟩ := evalSubst_equiv_open
          ((Γ.length, Expr.type, Expr.fix annB bodyB) :: S) Γ hev
        exact .unfold_fix_R (.trans (ih_sub _ _ _ _ h) hev_sub)
    | _ =>
      -- type, other: (_, _), isNeutral type = false → .ok false → contradiction
      unfold subCheckSubstMatch at h; simp [isNeutral] at h
  | asc ascE ascTy =>
    cases b with
    | iota annB bodyB =>
      -- asc, iota: (_, .iota) = iotaIntro
      unfold subCheckSubstMatch at h; simp only [Outcome.ok_bind] at h
      match hann : subCheckSubst n Γ ((Γ.length, Expr.asc ascE ascTy, Expr.iota annB bodyB) :: S) (Expr.asc ascE ascTy) annB with
      | .outOfFuel => rw [hann] at h; cases h
      | .error _ => rw [hann] at h; cases h
      | .ok annOk =>
        rw [hann] at h; simp only [Outcome.ok_bind] at h
        match annOk with
        | false => simp at h
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
          match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.asc ascE ascTy)) with
          | .outOfFuel => rw [hev] at h; simp at h
          | .error _ => rw [hev] at h; simp at h
          | .ok bodyB'' =>
            rw [hev] at h; simp only [] at h
            have hsub := ih_sub _ _ _ _ h
            refine .iota_intro (ih_sub _ _ _ _ hann) ?_
            exact hsub.trans (evalSubst_equiv_open _ Γ hev).1
    | fix annB bodyB =>
      -- asc, fix: (_, .fix) arm
      unfold subCheckSubstMatch at h; simp only [isNeutral, Outcome.ok_bind] at h
      match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.fix annB bodyB)) with
      | .outOfFuel => rw [hev] at h; simp at h
      | .error _ => rw [hev] at h; simp at h
      | .ok b' =>
        rw [hev] at h; simp only [] at h
        have hsub := ih_sub _ _ _ _ h
        refine .unfold_fix_R ?_
        exact hsub.trans (evalSubst_equiv_open _ Γ hev).1
    | _ =>
      -- asc, other: (_, _), isNeutral (asc ..) = false → .ok false → contradiction
      unfold subCheckSubstMatch at h; simp [isNeutral] at h
  | letE letV letB =>
    cases b with
    | iota annB bodyB =>
      -- letE, iota: (_, .iota) = iotaIntro
      unfold subCheckSubstMatch at h; simp only [Outcome.ok_bind] at h
      match hann : subCheckSubst n Γ ((Γ.length, Expr.letE letV letB, Expr.iota annB bodyB) :: S) (Expr.letE letV letB) annB with
      | .outOfFuel => rw [hann] at h; cases h
      | .error _ => rw [hann] at h; cases h
      | .ok annOk =>
        rw [hann] at h; simp only [Outcome.ok_bind] at h
        match annOk with
        | false => simp at h
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
          match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.letE letV letB)) with
          | .outOfFuel => rw [hev] at h; simp at h
          | .error _ => rw [hev] at h; simp at h
          | .ok bodyB'' =>
            rw [hev] at h; simp only [] at h
            have hsub := ih_sub _ _ _ _ h
            refine .iota_intro (ih_sub _ _ _ _ hann) ?_
            exact hsub.trans (evalSubst_equiv_open _ Γ hev).1
    | fix annB bodyB =>
      -- letE, fix: (_, .fix) arm
      unfold subCheckSubstMatch at h; simp only [isNeutral, Outcome.ok_bind] at h
      match hev : evalSubst (n + 1) unfBound (bodyB.subst 0 (Expr.fix annB bodyB)) with
      | .outOfFuel => rw [hev] at h; simp at h
      | .error _ => rw [hev] at h; simp at h
      | .ok b' =>
        rw [hev] at h; simp only [] at h
        have hsub := ih_sub _ _ _ _ h
        refine .unfold_fix_R ?_
        exact hsub.trans (evalSubst_equiv_open _ Γ hev).1
    | _ =>
      -- letE, other: (_, _), isNeutral (letE ..) = false → .ok false → contradiction
      unfold subCheckSubstMatch at h; simp [isNeutral] at h

/-! ## Soundness for `subCheckSubst` -/

/-- Helper: given that the if-then-else chain in `subCheckSubst` returns
    `.ok true`, produce the declarative subtype derivation.
    This factors out the common logic that applies regardless of whether
    the ascription-stripped forms came from `.asc` or not. -/
private noncomputable def subCheckSubst_ite_sound
    (n : Nat)
    (ih_sub : ∀ (Γ' : Ctx) (S' : Seen) (a' b' : Expr),
      subCheckSubst n Γ' S' a' b' = .ok true → Subtype' S' Γ' a' b')
    (Γ : Ctx) (S : Seen) (a'' b'' : Expr)
    (h : (if a'' == b'' then Outcome.ok true
          else if S.any (fun x => match x with | (_, av, bv) => a'' == av && b'' == bv) then Outcome.ok true
          else if b'' == Expr.type then Outcome.ok true
          else subCheckSubstMatch n Γ S a'' b'') = Outcome.ok true) :
    Subtype' S Γ a'' b'' := by
  by_cases heq : a'' == b''
  · have heq' : a'' = b'' := by simpa using heq
    exact heq' ▸ .refl _
  · simp only [heq, Bool.false_eq_true, ite_false] at h
    by_cases hseen : S.any (fun x => match x with | (_, av, bv) => a'' == av && b'' == bv)
    · -- Seen-set hit: needs depth-tag invariant (all entries in S
      -- have d ≤ Γ.length, and terms are shift-invariant at d = Γ.length)
      -- to connect to Subtype'.hyp. Sorry'd pending invariant propagation.
      sorry
    · simp only [hseen, Bool.false_eq_true, ite_false] at h
      by_cases htop : b'' == Expr.type
      · have htop' : b'' = .type := by simpa using htop
        exact htop' ▸ .top _
      · simp only [htop, Bool.false_eq_true, ite_false] at h
        exact subCheckSubstMatch_sound_gen n ih_sub Γ S a'' b'' h

set_option maxHeartbeats 800000

/-- Generalized soundness for `subCheckSubst` at any fuel/context/seen.

    The proof is by induction on fuel. At fuel `n+1`:
    1. Evaluate both sides to WHNF (eval bridge connects to original)
    2. Strip ascriptions (bridge via `asc_L_ann`, `asc_R`)
    3. Fast-path checks (equality → refl, seen → hyp, top → top)
    4. Delegate to `subCheckSubstMatch n` (IH provides soundness)

    Sorry'd: the equation-lemma unfolding for the mutual def creates
    match expressions that Lean's tactic mode can't cleanly destructure
    (overlapping `error`/`outOfFuel` patterns in the two-eval match).
    Each sub-obligation is independently closable. -/
private noncomputable def subCheckSubst_sound_gen
    (fuel : Nat) (Γ : Ctx) (S : Seen) (a b : Expr)
    (h : subCheckSubst fuel Γ S a b = .ok true) :
    Subtype' S Γ a b := by
  induction fuel generalizing Γ S a b with
  | zero => unfold subCheckSubst at h; cases h
  | succ n ih =>
    -- Unfold one step using the equation lemma
    rw [subCheckSubst.eq_def] at h; simp only [] at h
    -- Generalize and case-split on eval results
    generalize hea : evalSubst (n + 1) unfBound a = ra at h
    generalize heb : evalSubst (n + 1) unfBound b = rb at h
    cases ra with
    | outOfFuel => cases rb <;> simp_all
    | error s => cases rb <;> simp_all
    | ok a' =>
      cases rb with
      | outOfFuel => cases h
      | error s => cases h
      | ok b' =>
        -- h is about the let-if chain with asc stripping.
        -- simp to reduce the Outcome.ok match
        simp only [] at h
        -- Bridge: eval + asc strip
        have ⟨_, haa'⟩ := evalSubst_equiv_open S Γ hea
        have ⟨hb'b, _⟩ := evalSubst_equiv_open S Γ heb
        -- Case-split on a' to reduce the LHS asc-strip let binding in h,
        -- and on b' to reduce the RHS asc-strip let binding.
        -- After these cases, the matches in h reduce and we can apply ite_sound.
        cases a' with
        | asc _ ty =>
          cases b' with
          | asc e _ =>
            exact .trans haa' (.trans (.asc_L_ann (.refl _))
              (.trans (subCheckSubst_ite_sound n ih Γ S _ _ h)
              (.trans (.asc_R (.refl _)) hb'b)))
          | _ =>
            exact .trans haa' (.trans (.asc_L_ann (.refl _))
              (.trans (subCheckSubst_ite_sound n ih Γ S _ _ h) hb'b))
        | _ =>
          cases b' with
          | asc e _ =>
            exact .trans haa' (.trans (subCheckSubst_ite_sound n ih Γ S _ _ h)
              (.trans (.asc_R (.refl _)) hb'b))
          | _ =>
            exact .trans haa' (.trans (subCheckSubst_ite_sound n ih Γ S _ _ h) hb'b)

/-- The main soundness theorem for the structural subtype checker. -/
noncomputable def subCheckSubst_sound
    {fuel : Nat} {a b : Expr}
    (h : SubstEval.subCheck fuel a b = .ok true) :
    Subtype' [] [] a b := by
  simp only [SubstEval.subCheck] at h
  match ha : evalSubst fuel unfBound a with
  | .outOfFuel => rw [ha] at h; cases h
  | .error _ => rw [ha] at h; cases h
  | .ok a' =>
    match hb : evalSubst fuel unfBound b with
    | .outOfFuel => rw [ha, hb] at h; simp at h
    | .error _ => rw [ha, hb] at h; simp at h
    | .ok b' =>
      rw [ha, hb] at h; simp only [Outcome.ok_bind] at h
      have ⟨_, haa'⟩ := evalSubst_equiv_open [] [] ha
      have ⟨hb'b, _⟩ := evalSubst_equiv_open [] [] hb
      exact .trans haa' (.trans (subCheckSubst_sound_gen fuel [] [] a' b' h) hb'b)

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
