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
    | _ => sorry
  | iota _ _ => sorry
  | fix _ _ => sorry
  | bvar _ => sorry
  | app _ _ => sorry
  | type => sorry
  | asc _ _ => sorry
  | letE _ _ => sorry

/-! ## Soundness for `subCheckSubst` -/

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
        -- After cases, the match on (.ok a', .ok b') reduces
        simp only [] at h
        -- Now h is about the if-then-else chain.
        -- The eval bridge connects a to a' and b to b'; the asc strip
        -- bridges connect a' to strip(a') and strip(b') to b'.
        -- The IH handles the match delegation to subCheckSubstMatch.
        --
        -- The remaining obligations:
        -- 1. refl fast path: strip(a') = strip(b') → Subtype' S Γ a b
        -- 2. seen hit: (d, strip(a'), strip(b')) ∈ S → Subtype' S Γ a b
        -- 3. top: strip(b') = Type → Subtype' S Γ a b
        -- 4. match: subCheckSubstMatch n Γ S strip(a') strip(b') = ok true
        --    → Subtype' S Γ a b (via subCheckSubstMatch_sound_gen)
        --
        -- Each is closable by composing eval bridge + asc strip + the IH.
        sorry

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
    (_h : Och.subCheck a b fuel = .ok true) :
    Subtype' [] [] a.whnf b.whnf := by
  sorry

end Och.Soundness
