import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Monotonicity

Generalized to `absEval_mono` taking `Subtype' e₂ e₁` + `EnvSub Γ₂ Γ₁`.
Standard monotonicity is the corollary with `Subtype'.refl`.

Key technique: removing `trans` from `Subtype'` enables lambda inversion.
-/

open Expr

def EnvSub (Γ₂ Γ₁ : Env) : Prop :=
  ∀ x τ₁, Γ₁.lookup x = some τ₁ → ∃ τ₂, Γ₂.lookup x = some τ₂ ∧ Subtype' τ₂ τ₁

theorem envSub_extend {Γ₂ Γ₁ : Env} (h : EnvSub Γ₂ Γ₁) (x : Name) (v : Expr) :
    EnvSub ((x, v) :: Γ₂) ((x, v) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, Subtype'.refl v⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

theorem envSub_extend_sub {Γ₂ Γ₁ : Env} (h : EnvSub Γ₂ Γ₁)
    (x : Name) {v₂ v₁ : Expr} (hv : Subtype' v₂ v₁) :
    EnvSub ((x, v₂) :: Γ₂) ((x, v₁) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v₂, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

/-- **Generalized monotonicity.** -/
theorem absEval_mono
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e₁ e₂ τ₁ τ₂ : Expr)
    (h_sub : Subtype' e₂ e₁)
    (h_env : EnvSub Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e₁ = some τ₁)
    (h₂ : absEval fuel Γ₂ e₂ = some τ₂)
    : Subtype' τ₂ τ₁ := by
  induction fuel generalizing Γ₁ Γ₂ e₁ e₂ τ₁ τ₂ with
  | zero => simp [absEval] at h₁
  | succ n ih =>
    match h_sub with
    | .refl e =>
      cases e with
      | var x =>
        simp [absEval] at h₁ h₂
        have ⟨τ₂', h_l2, h_sub'⟩ := h_env x τ₁ h₁
        rw [h_l2] at h₂; cases h₂; exact h_sub'
      | lam x dom body =>
        simp only [absEval] at h₁ h₂
        cases hb₁ : absEval n ((x, .var x) :: Γ₁) body with
        | none => simp [hb₁] at h₁
        | some body₁ =>
          simp [hb₁] at h₁
          cases hb₂ : absEval n ((x, .var x) :: Γ₂) body with
          | none => simp [hb₂] at h₂
          | some body₂ =>
            simp [hb₂] at h₂; rw [← h₁, ← h₂]
            exact Subtype'.lam_body (ih _ _ body body _ _
              (Subtype'.refl body) (envSub_extend h_env x (.var x)) hb₁ hb₂)
      | type =>
        simp [absEval] at h₁ h₂; rw [← h₁, ← h₂]; exact Subtype'.refl .type
      | asc term ty =>
        simp only [absEval] at h₁ h₂
        exact ih _ _ ty ty _ _ (Subtype'.refl ty) h_env h₁ h₂
      | iota x body =>
        -- Structurally identical to the lam case
        simp only [absEval] at h₁ h₂
        cases hb₁ : absEval n ((x, .var x) :: Γ₁) body with
        | none => simp [hb₁] at h₁
        | some body₁ =>
          simp [hb₁] at h₁
          cases hb₂ : absEval n ((x, .var x) :: Γ₂) body with
          | none => simp [hb₂] at h₂
          | some body₂ =>
            simp [hb₂] at h₂; rw [← h₁, ← h₂]
            exact Subtype'.iota_body (ih _ _ body body _ _
              (Subtype'.refl body) (envSub_extend h_env x (.var x)) hb₁ hb₂)
      | fix inner =>
        simp only [absEval] at h₁ h₂
        cases inner with
        | lam f dom body =>
          -- absEval (.fix (.lam f dom body)) = absEval dom
          -- Both τ₁ and τ₂ come from evaluating dom in Γ₁ and Γ₂ respectively
          simp only at h₁ h₂
          exact ih _ _ dom dom _ _ (Subtype'.refl dom) h_env h₁ h₂
        | _ => simp at h₁
      | app f a =>
        simp only [absEval] at h₁ h₂
        cases hf₁ : absEval n Γ₁ f with
        | none => simp [hf₁] at h₁
        | some f₁ =>
          cases ha₁ : absEval n Γ₁ a with
          | none => simp [hf₁, ha₁] at h₁
          | some a₁ =>
            cases hf₂ : absEval n Γ₂ f with
            | none => simp [hf₂] at h₂
            | some f₂ =>
              cases ha₂ : absEval n Γ₂ a with
              | none => simp [hf₂, ha₂] at h₂
              | some a₂ =>
                have hf_sub := ih _ _ f f f₁ f₂ (Subtype'.refl f) h_env hf₁ hf₂
                have ha_sub := ih _ _ a a a₁ a₂ (Subtype'.refl a) h_env ha₁ ha₂
                -- Now case-split f₁ to know how absEval handled the app
                rw [hf₁, ha₁] at h₁; rw [hf₂, ha₂] at h₂
                cases f₁ with
                | lam x₁ dom₁ body₁ =>
                  -- f₁ is lam → f₂ must be lam by inversion
                  obtain ⟨body₂, hf₂_eq, hbody_sub⟩ := Subtype'.lam_rhs_shape hf_sub
                  subst hf₂_eq
                  -- h₁, h₂ now have matches on some(.lam..), which reduce
                  simp only at h₁ h₂
                  exact ih _ _ body₁ body₂ _ _ hbody_sub
                    (envSub_extend_sub h_env x₁ ha_sub) h₁ h₂
                | var v₁ =>
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub  -- Subtype' (lam ..) (var ..) impossible
                  | type => cases hf_sub       -- Subtype' .type (var ..) impossible
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact Subtype'.app_cong hf_sub ha_sub
                | app _ _ =>
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub
                  | type => cases hf_sub
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact Subtype'.app_cong hf_sub ha_sub
                | asc _ _ =>
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub
                  | type => cases hf_sub
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact Subtype'.app_cong hf_sub ha_sub
                | fix _ =>
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub
                  | type => cases hf_sub
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact Subtype'.app_cong hf_sub ha_sub
                | iota _ _ =>
                  cases f₂ with
                  | lam _ _ _ => cases hf_sub
                  | type => cases hf_sub
                  | _ => simp only at h₁ h₂; cases h₁; cases h₂
                         exact Subtype'.app_cong hf_sub ha_sub
                | type =>
                  -- f₁=.type: evaluator returns .type (type-app-returns-type)
                  simp only at h₁; cases h₁; exact Subtype'.top τ₂
    | .top e =>
      simp [absEval] at h₁; rw [← h₁]; exact Subtype'.top τ₂
    | .lam_body hbody =>
      rename_i x dom body₁ body₂
      simp only [absEval] at h₁ h₂
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body₁ with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        simp [hb₁] at h₁
        cases hb₂ : absEval n ((x, .var x) :: Γ₂) body₂ with
        | none => simp [hb₂] at h₂
        | some body₂' =>
          simp [hb₂] at h₂; rw [← h₁, ← h₂]
          exact Subtype'.lam_body (ih _ _ body₁ body₂ _ _ hbody
            (envSub_extend h_env x (.var x)) hb₁ hb₂)
    | .app_cong hf ha =>
      rename_i e1_f e2_f e1_a e2_a
      simp only [absEval] at h₁ h₂
      cases hf₁ : absEval n Γ₁ e1_f with
      | none => simp [hf₁] at h₁
      | some f₁ =>
        cases ha₁ : absEval n Γ₁ e1_a with
        | none => simp [hf₁, ha₁] at h₁
        | some a₁ =>
          cases hf₂ : absEval n Γ₂ e2_f with
          | none => simp [hf₂] at h₂
          | some f₂ =>
            cases ha₂ : absEval n Γ₂ e2_a with
            | none => simp [hf₂, ha₂] at h₂
            | some a₂ =>
              have hf_sub := ih _ _ _ _ f₁ f₂ hf h_env hf₁ hf₂
              have ha_sub := ih _ _ _ _ a₁ a₂ ha h_env ha₁ ha₂
              rw [hf₁, ha₁] at h₁; rw [hf₂, ha₂] at h₂
              cases f₁ with
              | lam x₁ dom₁ body₁ =>
                obtain ⟨body₂, hf₂_eq, hbody_sub⟩ := Subtype'.lam_rhs_shape hf_sub
                subst hf₂_eq
                simp only at h₁ h₂
                exact ih _ _ body₁ body₂ _ _ hbody_sub
                  (envSub_extend_sub h_env x₁ ha_sub) h₁ h₂
              | var v₁ =>
                cases f₂ with
                | lam _ _ _ => cases hf_sub
                | type => cases hf_sub
                | _ => simp only at h₁ h₂; cases h₁; cases h₂
                       exact Subtype'.app_cong hf_sub ha_sub
              | app _ _ =>
                cases f₂ with
                | lam _ _ _ => cases hf_sub
                | type => cases hf_sub
                | _ => simp only at h₁ h₂; cases h₁; cases h₂
                       exact Subtype'.app_cong hf_sub ha_sub
              | asc _ _ =>
                cases f₂ with
                | lam _ _ _ => cases hf_sub
                | type => cases hf_sub
                | _ => simp only at h₁ h₂; cases h₁; cases h₂
                       exact Subtype'.app_cong hf_sub ha_sub
              | fix _ =>
                cases f₂ with
                | lam _ _ _ => cases hf_sub
                | type => cases hf_sub
                | _ => simp only at h₁ h₂; cases h₁; cases h₂
                       exact Subtype'.app_cong hf_sub ha_sub
              | iota _ _ =>
                cases f₂ with
                | lam _ _ _ => cases hf_sub
                | type => cases hf_sub
                | _ => simp only at h₁ h₂; cases h₁; cases h₂
                       exact Subtype'.app_cong hf_sub ha_sub
              | type =>
                -- f₁=.type: evaluator returns .type (type-app-returns-type)
                simp only at h₁; cases h₁; exact Subtype'.top τ₂
    | .fix_cong h_inner =>
      rename_i inner₁ inner₂
      simp only [absEval] at h₁ h₂
      -- inner₁ must be a lam (else absEval returns none, contradicting h₁)
      -- Subtype' inner₂ inner₁ → inner₂ has same shape (lam with same dom)
      -- Both sides return absEval of the same dom → IH on dom
      cases inner₁ with
      | lam f₁ dom₁ body₁ =>
        obtain ⟨body₂, hinner₂_eq, _⟩ := Subtype'.lam_rhs_shape h_inner
        subst hinner₂_eq
        -- Both: absEval n Γ dom₁ (same domain by lam_rhs_shape)
        simp only at h₁ h₂
        exact ih _ _ dom₁ dom₁ _ _ (Subtype'.refl dom₁) h_env h₁ h₂
      | _ =>
        -- inner₁ not a lam: absEval returns none, contradiction
        simp at h₁
    | .iota_body hbody =>
      -- Structurally identical to the lam_body case
      rename_i x body₁ body₂
      simp only [absEval] at h₁ h₂
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body₁ with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        simp [hb₁] at h₁
        cases hb₂ : absEval n ((x, .var x) :: Γ₂) body₂ with
        | none => simp [hb₂] at h₂
        | some body₂' =>
          simp [hb₂] at h₂; rw [← h₁, ← h₂]
          exact Subtype'.iota_body (ih _ _ body₁ body₂ _ _ hbody
            (envSub_extend h_env x (.var x)) hb₁ hb₂)

theorem monotonicity
    (Γ₁ Γ₂ : Env) (e τ₁ τ₂ : Expr) (fuel : Nat)
    (h_env : EnvSub Γ₂ Γ₁)
    (h_abs₁ : absEval fuel Γ₁ e = some τ₁)
    (h_abs₂ : absEval fuel Γ₂ e = some τ₂)
    : Subtype' τ₂ τ₁ :=
  absEval_mono fuel Γ₁ Γ₂ e e τ₁ τ₂ (Subtype'.refl e) h_env h_abs₁ h_abs₂

-- ============================================================
-- Generalized monotonicity with SubtypeTrans
-- ============================================================

/-- Environment subtyping via SubtypeTrans (transitive closure). -/
def EnvSubTrans (Γ₂ Γ₁ : Env) : Prop :=
  ∀ x τ₁, Γ₁.lookup x = some τ₁ → ∃ τ₂, Γ₂.lookup x = some τ₂ ∧ SubtypeTrans τ₂ τ₁

/-- An env is "closed" if every free variable in every env value is bound in the env.
    This excludes envs like [(y, λx:Type. z)] where z is unbound — these never
    arise from well-formed evaluation but aren't ruled out by EnvSubTrans. -/
def EnvClosed (Γ : Env) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → ∀ y, y ∈ τ.freeVars → Γ.lookup y ≠ none

/-- Extending a closed env with a binding whose value has free vars covered by the
    extended env preserves closedness. -/
theorem envClosed_extend {Γ : Env} (h : EnvClosed Γ)
    (x : Name) (v : Expr) (hv : ∀ y, y ∈ v.freeVars → Env.lookup ((x, v) :: Γ) y ≠ none) :
    EnvClosed ((x, v) :: Γ) := by
  intro z τ h_lookup y hy
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup
  · -- z = x, so τ = v
    cases h_lookup; exact hv y hy
  · -- z ≠ x, so τ is from Γ
    have h_old := h z τ h_lookup y hy
    split
    · -- y = x → found
      exact fun h => absurd h (by simp)
    · exact h_old

/-- Free vars in an env value are covered by the env (if EnvClosed). -/
theorem envClosed_freeVars {Γ : Env} {x : Name} {τ : Expr}
    (h_closed : EnvClosed Γ) (h_lookup : Γ.lookup x = some τ) :
    ∀ y, y ∈ τ.freeVars → Γ.lookup y ≠ none :=
  h_closed x τ h_lookup

/-- Extending an env with (x, var x) preserves closedness: var x has freeVars = [x],
    which is covered by the extended env since x is the new binding. -/
theorem envClosed_extend_var {Γ : Env} (h : EnvClosed Γ) (x : Name) :
    EnvClosed ((x, .var x) :: Γ) := by
  apply envClosed_extend h
  intro y hy
  simp [Expr.freeVars, List.mem_singleton] at hy
  subst hy
  simp [Env.lookup]

/-- If Γ.lookup y ≠ none then extending the env preserves this. -/
private theorem lookup_extend_of_lookup {Γ : Env} {x : Name} {v : Expr} {y : Name}
    (h : Γ.lookup y ≠ none) : Env.lookup ((x, v) :: Γ) y ≠ none := by
  simp only [Env.lookup]
  split
  · simp
  · exact h

/-- If y ≠ x and ((x, v) :: Γ).lookup y ≠ none, then Γ.lookup y ≠ none. -/
private theorem lookup_of_lookup_extend {Γ : Env} {x y : Name} {v : Expr}
    (h : Env.lookup ((x, v) :: Γ) y ≠ none) (hne : x ≠ y) : Γ.lookup y ≠ none := by
  simp only [Env.lookup] at h
  rw [show (x == y) = false from by simp [beq_iff_eq, hne]] at h
  exact h

/-- freeVars of body are covered by ((x, v) :: Γ) when
    freeVars of (lam x dom body) are covered by Γ. Works for any v. -/
private theorem body_freeVars_covered_by_extend {Γ : Env} {x : Name} {dom body v : Expr}
    (h_fv : ∀ y, y ∈ (Expr.lam x dom body).freeVars → Γ.lookup y ≠ none) :
    ∀ y, y ∈ body.freeVars → Env.lookup ((x, v) :: Γ) y ≠ none := by
  intro y hy
  by_cases hxy : x = y
  · subst hxy; simp [Env.lookup]
  · exact lookup_extend_of_lookup (h_fv y (by
      simp [Expr.freeVars, List.mem_append, List.mem_filter]
      exact Or.inr ⟨hy, Ne.symm hxy⟩))

/-- freeVars of body are covered by ((x, v) :: Γ) when
    body.freeVars.filter(·!=x) are covered by Γ (for iota case). -/
private theorem iota_body_freeVars_covered_by_extend {Γ : Env} {x : Name} {body v : Expr}
    (h_fv : ∀ y, y ∈ (Expr.iota x body).freeVars → Γ.lookup y ≠ none) :
    ∀ y, y ∈ body.freeVars → Env.lookup ((x, v) :: Γ) y ≠ none := by
  intro y hy
  by_cases hxy : x = y
  · subst hxy; simp [Env.lookup]
  · exact lookup_extend_of_lookup (h_fv y (by
      simp [Expr.freeVars, List.mem_filter]
      exact ⟨hy, Ne.symm hxy⟩))

/-- ⚠ FALSE for app-lam case — see CounterexampleTest.lean.

    The theorem claims: if absEval succeeds and the env is closed, the output's
    freeVars are covered by the env. This is FALSE because absEval does NOT evaluate
    domain annotations in lambdas. After beta-reduction, the body may contain nested
    lambdas whose domain annotations reference the (now-gone) binder variable.

    Counterexample: Γ = [], e = (λx:Type. λy:x. y) Type → τ = λy:(var x). y.
    "x" is free in τ but not in Γ.

    Cases proved: var, type, asc, fix, lam, iota (all correct).
    False case: app-lam (domain annotations leak stale variable references).

    This blocks the freeVars/EnvClosed approach to fixing absEval_succeeds_envsub.
    Alternative: build absEvalC (closure-based abstract evaluator) or track
    "evaluable vars" separately from domain annotation vars. -/
theorem absEval_freeVars_covered
    (fuel : Nat) (Γ : Env) (e τ : Expr)
    (h_closed : EnvClosed Γ)
    (h_eval : absEval fuel Γ e = some τ)
    (h_fv : ∀ x, x ∈ e.freeVars → Γ.lookup x ≠ none)
    : ∀ x, x ∈ τ.freeVars → Γ.lookup x ≠ none := by
  induction fuel generalizing Γ e τ with
  | zero => simp [absEval] at h_eval
  | succ n ih =>
    cases e with
    | var x =>
      simp only [absEval] at h_eval
      exact h_closed x τ h_eval
    | type =>
      simp only [absEval] at h_eval; cases h_eval
      intro x hx; simp [Expr.freeVars] at hx
    | asc term ty =>
      simp only [absEval] at h_eval
      exact ih Γ ty τ h_closed h_eval (fun x hx => h_fv x (List.mem_append_right _ hx))
    | fix inner =>
      simp only [absEval] at h_eval
      cases inner with
      | lam f dom body =>
        exact ih Γ dom τ h_closed h_eval (fun y hy =>
          h_fv y (by simp [Expr.freeVars, List.mem_append]; exact Or.inl hy))
      | _ => simp [absEval] at h_eval
    | lam x dom body =>
      simp only [absEval] at h_eval
      cases hb : absEval n ((x, .var x) :: Γ) body with
      | none => simp [hb] at h_eval
      | some body' =>
        rw [hb] at h_eval; simp at h_eval; subst h_eval
        intro y hy
        -- (.lam x dom body').freeVars = dom.freeVars ++ body'.freeVars.filter(·!=x)
        rcases List.mem_append.mp hy with h_dom | h_body
        · -- y ∈ dom.freeVars
          exact h_fv y (List.mem_append_left _ h_dom)
        · -- y ∈ body'.freeVars.filter(·!=x)
          have ⟨h_mem, h_ne⟩ := List.mem_filter.mp h_body
          -- IH: body'.freeVars covered by ((x, .var x) :: Γ)
          have h_ext := ih ((x, .var x) :: Γ) body body'
            (envClosed_extend_var h_closed x) hb
            (body_freeVars_covered_by_extend h_fv) y h_mem
          -- h_ne : (y != x) = true, so y ≠ x
          have h_ne' : x ≠ y := by
            intro heq; subst heq
            simp [bne_iff_ne] at h_ne
          exact lookup_of_lookup_extend h_ext h_ne'
    | iota x body =>
      simp only [absEval] at h_eval
      cases hb : absEval n ((x, .var x) :: Γ) body with
      | none => simp [hb] at h_eval
      | some body' =>
        rw [hb] at h_eval; simp at h_eval; subst h_eval
        intro y hy
        -- (.iota x body').freeVars = body'.freeVars.filter(·!=x)
        have ⟨h_mem, h_ne⟩ := List.mem_filter.mp hy
        have h_ext := ih ((x, .var x) :: Γ) body body'
          (envClosed_extend_var h_closed x) hb
          (iota_body_freeVars_covered_by_extend h_fv) y h_mem
        have h_ne' : x ≠ y := by
          intro heq; subst heq
          simp [bne_iff_ne] at h_ne
        exact lookup_of_lookup_extend h_ext h_ne'
    | app f a =>
      simp only [absEval] at h_eval
      cases hf : absEval n Γ f with
      | none => simp [hf] at h_eval
      | some f' =>
        cases ha : absEval n Γ a with
        | none => simp [hf, ha] at h_eval
        | some a' =>
          have h_fv_f := ih Γ f f' h_closed hf
            (fun y hy => h_fv y (List.mem_append_left _ hy))
          have h_fv_a := ih Γ a a' h_closed ha
            (fun y hy => h_fv y (List.mem_append_right _ hy))
          rw [hf, ha] at h_eval
          cases f' with
          | lam x dom body =>
            -- result = absEval n ((x, a') :: Γ) body
            have h_closed_ext : EnvClosed ((x, a') :: Γ) :=
              envClosed_extend h_closed x a'
                (fun y hy => lookup_extend_of_lookup (h_fv_a y hy))
            have h_body_fv : ∀ z, z ∈ body.freeVars →
                Env.lookup ((x, a') :: Γ) z ≠ none :=
              body_freeVars_covered_by_extend h_fv_f
            -- IH gives coverage by ((x, a') :: Γ). Bridge to Γ:
            have h_ext := ih ((x, a') :: Γ) body τ h_closed_ext h_eval h_body_fv
            intro y hy
            have h_covered := h_ext y hy
            by_cases hxy : x = y
            · -- y = x. If x ∈ Γ we're done. If not, need x ∉ τ.freeVars.
              subst hxy
              -- x might or might not be in Γ. If Γ has x, done.
              by_cases h_in_Γ : Γ.lookup x = none
              · -- ⚠ THEOREM IS FALSE for this case.
                -- Counterexample: Γ = [], e = (λx:Type. λy:x. y) Type
                -- absEval returns λy:(var x). y, which has "x" free,
                -- but [].lookup "x" = none.
                -- Root cause: domain annotations in lambdas are NOT evaluated
                -- by absEval, so they can contain stale variable references.
                -- See CounterexampleTest.lean for Lean-verified counterexample.
                sorry
              · exact h_in_Γ
            · exact lookup_of_lookup_extend h_covered hxy
          | type =>
            simp at h_eval; subst h_eval
            intro y hy; simp [Expr.freeVars] at hy
          | var _ | app _ _ | asc _ _ | fix _ | iota _ _ =>
            simp at h_eval; subst h_eval
            intro y hy
            rcases List.mem_append.mp hy with h1 | h2
            · exact h_fv_f y h1
            · exact h_fv_a y h2

theorem envSubTrans_extend {Γ₂ Γ₁ : Env} (h : EnvSubTrans Γ₂ Γ₁) (x : Name) (v : Expr) :
    EnvSubTrans ((x, v) :: Γ₂) ((x, v) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v, rfl, SubtypeTrans.step (Subtype'.refl v)⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

theorem envSubTrans_extend_sub {Γ₂ Γ₁ : Env} (h : EnvSubTrans Γ₂ Γ₁)
    (x : Name) {v₂ v₁ : Expr} (hv : SubtypeTrans v₂ v₁) :
    EnvSubTrans ((x, v₂) :: Γ₂) ((x, v₁) :: Γ₁) := by
  intro y τ₁ h_lookup
  simp only [Env.lookup] at h_lookup ⊢
  split at h_lookup <;> split
  · cases h_lookup; exact ⟨v₂, rfl, hv⟩
  · rename_i h1 h2; exact absurd h1 h2
  · rename_i h1 h2; exact absurd h2 h1
  · exact h y τ₁ h_lookup

/-- **Generalized monotonicity with SubtypeTrans.**

    Same structure as `soundness_gen`: induction on fuel, case split on e₁
    (the abstract/wider expression), use SubtypeTrans target shape lemmas
    to constrain e₂.

    This is the SubtypeTrans analogue of `absEval_mono`. The key difference:
    - `absEval_mono` takes `Subtype' e₂ e₁` + `EnvSub`, returns `Subtype'`
    - `absEval_mono_trans` takes `SubtypeTrans e₂ e₁` + `EnvSubTrans`, returns `SubtypeTrans`

    The app-beta case is handled by case-splitting on e₁, NOT on h_sub.
    SubtypeTrans.lam_target_shape gives the body relationship, and the IH
    at lower fuel handles the recursive call with SubtypeTrans bodies+envs. -/
theorem absEval_mono_trans
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e₁ e₂ τ₁ τ₂ : Expr)
    (h_sub : SubtypeTrans e₂ e₁)
    (h_env : EnvSubTrans Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e₁ = some τ₁)
    (h₂ : absEval fuel Γ₂ e₂ = some τ₂)
    : SubtypeTrans τ₂ τ₁ := by
  induction fuel generalizing Γ₁ Γ₂ e₁ e₂ τ₁ τ₂ with
  | zero => simp [absEval] at h₁
  | succ n ih =>
    cases e₁ with
    | var x =>
      have := h_sub.var_target; subst this
      simp [absEval] at h₁ h₂
      have ⟨τ₂', h_l2, h_sub'⟩ := h_env x τ₁ h₁
      rw [h_l2] at h₂; cases h₂; exact h_sub'
    | type =>
      simp [absEval] at h₁; rw [← h₁]
      exact SubtypeTrans.step (Subtype'.top τ₂)
    | lam x dom body₁ =>
      obtain ⟨body₂, hec_eq, h_body_sub⟩ := h_sub.lam_target_shape
      subst hec_eq
      simp only [absEval] at h₁ h₂
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body₁ with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        simp [hb₁] at h₁
        cases hb₂ : absEval n ((x, .var x) :: Γ₂) body₂ with
        | none => simp [hb₂] at h₂
        | some body₂' =>
          simp [hb₂] at h₂; rw [← h₁, ← h₂]
          exact SubtypeTrans.lam_body (ih _ _ body₁ body₂ _ _ h_body_sub
            (envSubTrans_extend h_env x (.var x)) hb₁ hb₂)
    | asc term ty =>
      have := h_sub.asc_target; subst this
      simp only [absEval] at h₁ h₂
      exact ih _ _ ty ty _ _ (SubtypeTrans.step (Subtype'.refl ty)) h_env h₁ h₂
    | iota x body₁ =>
      obtain ⟨body₂, hec_eq, h_body_sub⟩ := h_sub.iota_target_shape
      subst hec_eq
      simp only [absEval] at h₁ h₂
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body₁ with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        simp [hb₁] at h₁
        cases hb₂ : absEval n ((x, .var x) :: Γ₂) body₂ with
        | none => simp [hb₂] at h₂
        | some body₂' =>
          simp [hb₂] at h₂; rw [← h₁, ← h₂]
          exact SubtypeTrans.iota_body (ih _ _ body₁ body₂ _ _ h_body_sub
            (envSubTrans_extend h_env x (.var x)) hb₁ hb₂)
    | fix inner₁ =>
      obtain ⟨inner₂, hec_eq, h_inner_sub⟩ := h_sub.fix_target_shape
      subst hec_eq
      simp only [absEval] at h₁ h₂
      cases inner₁ with
      | lam f₁ dom₁ body₁ =>
        obtain ⟨body₂, hinner₂_eq, _⟩ := h_inner_sub.lam_target_shape
        subst hinner₂_eq
        -- Both sides evaluate dom₁ (same domain by lam_target_shape)
        simp only at h₁ h₂
        exact ih _ _ dom₁ dom₁ _ _ (SubtypeTrans.step (Subtype'.refl dom₁)) h_env h₁ h₂
      | _ => simp at h₁
    | app f₁ a₁ =>
      obtain ⟨f₂, a₂, hec_eq, h_f_sub, h_a_sub⟩ := h_sub.app_target_shape
      subst hec_eq
      simp only [absEval] at h₁ h₂
      cases hf₁ : absEval n Γ₁ f₁ with
      | none => simp [hf₁] at h₁
      | some τ_f₁ =>
        cases ha₁ : absEval n Γ₁ a₁ with
        | none => simp [hf₁, ha₁] at h₁
        | some τ_a₁ =>
          cases hf₂ : absEval n Γ₂ f₂ with
          | none => simp [hf₂] at h₂
          | some τ_f₂ =>
            cases ha₂ : absEval n Γ₂ a₂ with
            | none => simp [hf₂, ha₂] at h₂
            | some τ_a₂ =>
              have ih_f := ih _ _ f₁ f₂ _ _ h_f_sub h_env hf₁ hf₂
              have ih_a := ih _ _ a₁ a₂ _ _ h_a_sub h_env ha₁ ha₂
              rw [hf₁, ha₁] at h₁; rw [hf₂, ha₂] at h₂
              cases τ_f₁ with
              | lam x₁ dom₁ body₁ =>
                obtain ⟨body₂, hf₂_eq, hbody_sub⟩ := ih_f.lam_target_shape
                subst hf₂_eq
                simp only at h₁ h₂
                exact ih _ _ body₁ body₂ _ _ hbody_sub
                  (envSubTrans_extend_sub h_env x₁ ih_a) h₁ h₂
              | type =>
                simp only at h₁; cases h₁
                exact SubtypeTrans.step (Subtype'.top τ₂)
              | var v₁ =>
                have := ih_f.var_target; subst this
                simp only at h₁ h₂; cases h₁; cases h₂
                exact SubtypeTrans.app_cong ih_f ih_a
              | app f₁' a₁' =>
                obtain ⟨f₂', a₂', hvf_eq, _, _⟩ := ih_f.app_target_shape
                subst hvf_eq
                simp only at h₁ h₂; cases h₁; cases h₂
                exact SubtypeTrans.app_cong ih_f ih_a
              | asc t' τ' =>
                have := ih_f.asc_target; subst this
                simp only at h₁ h₂; cases h₁; cases h₂
                exact SubtypeTrans.app_cong ih_f ih_a
              | fix inner' =>
                obtain ⟨inner₂', _, _⟩ := ih_f.fix_target_shape
                subst ‹τ_f₂ = .fix inner₂'›
                simp only at h₁ h₂; cases h₁; cases h₂
                exact SubtypeTrans.app_cong ih_f ih_a
              | iota x' body' =>
                obtain ⟨body₂', _, _⟩ := ih_f.iota_target_shape
                subst ‹τ_f₂ = .iota x' body₂'›
                simp only at h₁ h₂; cases h₁; cases h₂
                exact SubtypeTrans.app_cong ih_f ih_a

/-- Standard monotonicity corollary with SubtypeTrans envs. -/
theorem monotonicity_trans
    (Γ₁ Γ₂ : Env) (e τ₁ τ₂ : Expr) (fuel : Nat)
    (h_env : EnvSubTrans Γ₂ Γ₁)
    (h_abs₁ : absEval fuel Γ₁ e = some τ₁)
    (h_abs₂ : absEval fuel Γ₂ e = some τ₂)
    : SubtypeTrans τ₂ τ₁ :=
  absEval_mono_trans fuel Γ₁ Γ₂ e e τ₁ τ₂ (SubtypeTrans.step (Subtype'.refl e))
    h_env h_abs₁ h_abs₂

/-- **Totality under env narrowing (same expression).**

    If absEval succeeds in Γ₁ with expression e, and Γ₂ ⊑ Γ₁ (EnvSubTrans),
    then absEval succeeds in Γ₂ with the same expression. Together with
    `monotonicity_trans`, this gives the full "mono + succeed" package.

    **⚠ THIS THEOREM IS FALSE AS STATED.** See `CounterexampleTest.lean` for a
    concrete counterexample where Γ₂ = [(y, λx:Type. z)] (z unbound) and
    Γ₁ = [(y, Type)]. EnvSubTrans holds via `top`, absEval succeeds in Γ₁
    (Type applied = Type) but fails in Γ₂ (z not in scope during beta-reduction).

    The issue: EnvSubTrans has no well-formedness requirement — env values can
    contain free variables not bound in the env. In practice, envs built by
    absEval are well-formed (normalization under binders would have failed for
    unbound vars), but this isn't captured by the theorem's hypotheses.

    **Fix approaches — EnvClosed is NOT sufficient:**
    `absEval_freeVars_covered` (which would support EnvClosed) is itself FALSE
    for the app-lam case — domain annotations in lambdas are not evaluated, so
    they can contain stale variable references. See CounterexampleTest.lean.

    Viable alternatives:
    1. Build absEvalC (closure-based abstract evaluator, SUGGESTIONS.md item 2)
       which avoids the body normalization mismatch entirely
    2. Track "evaluable vars" (vars in positions absEval will actually look up)
       separately from domain annotation vars
    3. Restrict to envs produced by absEval at each use site

    **Status:** All cases proved EXCEPT app-lam. The sorry is specifically for:
    when f evaluates to a lambda in Γ₂ but to Type in Γ₁, there's no Γ₁-side
    body evaluation to bootstrap from. -/
theorem absEval_succeeds_envsub
    (fuel : Nat) (Γ₁ Γ₂ : Env) (e τ₁ : Expr)
    (h_env : EnvSubTrans Γ₂ Γ₁)
    (h₁ : absEval fuel Γ₁ e = some τ₁)
    : ∃ τ₂, absEval fuel Γ₂ e = some τ₂ := by
  induction fuel generalizing Γ₁ Γ₂ e τ₁ with
  | zero => simp [absEval] at h₁
  | succ n ih =>
    cases e with
    | var x =>
      simp only [absEval] at h₁ ⊢
      obtain ⟨τ₂, h_l2, _⟩ := h_env x τ₁ h₁
      exact ⟨τ₂, h_l2⟩
    | type =>
      exact ⟨.type, rfl⟩
    | lam x dom body =>
      simp only [absEval] at h₁ ⊢
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        have ⟨body₂', hb₂⟩ := ih ((x, .var x) :: Γ₁) ((x, .var x) :: Γ₂) body body₁'
          (envSubTrans_extend h_env x (.var x)) hb₁
        rw [hb₂]; exact ⟨_, rfl⟩
    | asc term ty =>
      simp only [absEval] at h₁ ⊢
      exact ih Γ₁ Γ₂ ty τ₁ h_env h₁
    | iota x body =>
      simp only [absEval] at h₁ ⊢
      cases hb₁ : absEval n ((x, .var x) :: Γ₁) body with
      | none => simp [hb₁] at h₁
      | some body₁' =>
        have ⟨body₂', hb₂⟩ := ih ((x, .var x) :: Γ₁) ((x, .var x) :: Γ₂) body body₁'
          (envSubTrans_extend h_env x (.var x)) hb₁
        rw [hb₂]; exact ⟨_, rfl⟩
    | fix inner =>
      simp only [absEval] at h₁ ⊢
      cases inner with
      | lam f dom body =>
        exact ih Γ₁ Γ₂ dom τ₁ h_env h₁
      | _ => simp [absEval] at h₁
    | app f a =>
      simp only [absEval] at h₁ ⊢
      cases hf₁ : absEval n Γ₁ f with
      | none => simp [hf₁] at h₁
      | some τ_f₁ =>
        cases ha₁ : absEval n Γ₁ a with
        | none => simp [hf₁, ha₁] at h₁
        | some τ_a₁ =>
          -- IH: sub-evals succeed in Γ₂
          obtain ⟨τ_f₂, hf₂⟩ := ih Γ₁ Γ₂ f τ_f₁ h_env hf₁
          obtain ⟨τ_a₂, ha₂⟩ := ih Γ₁ Γ₂ a τ_a₁ h_env ha₁
          -- Monotonicity gives shape relationship: τ_f₂ ⊑ τ_f₁
          have h_f_sub := monotonicity_trans Γ₁ Γ₂ f τ_f₁ τ_f₂ n h_env hf₁ hf₂
          rw [hf₁, ha₁] at h₁
          -- Case split on τ_f₂ (which appears in the goal after rw)
          rw [hf₂, ha₂]
          cases τ_f₂ with
          | lam x dom body₂ =>
            -- τ_f₂ is lam → beta-reduce in Γ₂. Need body eval to succeed.
            simp only
            -- Get SubtypeTrans on a for env extension
            have h_a_sub := monotonicity_trans Γ₁ Γ₂ a τ_a₁ τ_a₂ n h_env ha₁ ha₂
            -- SubtypeTrans (lam x dom body₂) τ_f₁ → τ_f₁ = lam x dom body₁ or type
            -- Use lam_lhs to get the two possible shapes of τ_f₁
            -- For now, sorry the whole lam sub-case (needs generalized IH for body₂ ≠ body₁)
            sorry
          | type =>
            simp only; exact ⟨.type, rfl⟩
          | var _ =>
            simp only; exact ⟨_, rfl⟩
          | app _ _ =>
            simp only; exact ⟨_, rfl⟩
          | asc _ _ =>
            simp only; exact ⟨_, rfl⟩
          | fix _ =>
            simp only; exact ⟨_, rfl⟩
          | iota _ _ =>
            simp only; exact ⟨_, rfl⟩

-- ============================================================
-- evalFreeVars coverage: absEval outputs have evalFreeVars ⊆ neutralVars(Γ)
-- ============================================================

/-!
### Why evalFreeVars, not freeVars?

`absEval_freeVars_covered` (using standard `freeVars`) is FALSE for the app-lam
case because domain annotations in lambdas are not evaluated by absEval and can
contain stale variable references after beta-reduction.

`evalFreeVars` (Syntax.lean) excludes domain annotations, matching what absEval
actually looks up. This makes the coverage theorem TRUE for ALL cases.

### Key insight: neutral vars

The theorem says: evalFreeVars(τ) ⊆ neutralVars(Γ), where
neutralVars(Γ) = {x | Γ.lookup x = some (var x)}.

This is STRONGER than ⊆ dom(Γ) and is needed for the app-lam case:
- After beta-reducing (lam x dom body) τ_a in env ((x, τ_a) :: Γ):
- IH gives evalFreeVars(result) ⊆ neutralVars((x, τ_a) :: Γ)
- If τ_a ≠ var x: x is non-neutral → x ∉ result. neutralVars ⊆ neutralVars(Γ).
- If τ_a = var x: x IS neutral. By IH on a, x ∈ neutralVars(Γ). Still ⊆ dom(Γ).

### Caveat: env extension and shadowing

`envEvalClosed'_extend_value` is only correct when x does not shadow a neutral
variable in Γ. For well-scoped source code with distinct binder names (no
shadowing), this is not an issue. A NoShadowing precondition or de Bruijn
indices would make this airtight.

### Proof status

The proof structure is fully worked out. The sorry's below are BEq/String
plumbing issues in Lean 4 (converting between `(x == y) = true` and `x = y`
for `String`), not conceptual gaps. The proof strategy:
- var: direct from EnvEvalClosed'
- type: trivial (empty evalFreeVars)
- asc, fix: IH on sub-expression
- lam, iota: IH on body with neutral extension, filter out binder
- app-lam: IH on body with value extension, map neutral back to outer env
- app-stuck: IH on f and a, combine via List.mem_append
-/

/-- A variable is "neutral" in an env if it maps to itself. Only neutral variables
    can appear free in absEval outputs (non-neutral ones get resolved). -/
def isNeutral (Γ : Env) (x : Name) : Prop :=
  Γ.lookup x = some (.var x)

/-- An env is "eval-closed" if every env value's evalFreeVars are neutral. -/
def EnvEvalClosed' (Γ : Env) : Prop :=
  ∀ x v, Γ.lookup x = some v → ∀ y, y ∈ v.evalFreeVars → isNeutral Γ y

/-- Extending an eval-closed env with a neutral binding preserves closedness. -/
theorem envEvalClosed'_extend_neutral {Γ : Env} (h : EnvEvalClosed' Γ) (x : Name) :
    EnvEvalClosed' ((x, .var x) :: Γ) := by
  intro y v h_lookup z h_z_free
  simp only [Env.lookup] at h_lookup
  simp only [isNeutral, Env.lookup]
  split at h_lookup <;> rename_i h_eq
  · -- y = x: v = var x
    cases h_lookup
    simp [Expr.evalFreeVars] at h_z_free
    subst h_z_free
    simp [h_eq]
  · -- y ≠ x: v from Γ
    have h_neutral := h y v h_lookup z h_z_free
    simp only [isNeutral, Env.lookup] at h_neutral
    split
    · -- z = x in extended env: we return var x. Need some (var x) = some (var z).
      -- Since z == x is true, z and x are BEq-equal.
      rename_i h_zx
      -- For String, BEq is equality. h_zx : (x == z) = true
      have : x = z := by exact beq_iff_eq.mp h_zx
      rw [this]
    · exact h_neutral

/-- Extending an eval-closed env with a value whose evalFreeVars are neutral
    preserves closedness, provided x is fresh (not already in Γ).

    The freshness condition prevents shadowing: if x were already neutral in Γ
    (Γ.lookup x = some (var x)), overwriting with v ≠ var x would break the
    invariant for existing values that reference x. -/
theorem envEvalClosed'_extend_value {Γ : Env} (h : EnvEvalClosed' Γ) (x : Name) (v : Expr)
    (h_v : ∀ y, y ∈ v.evalFreeVars → isNeutral Γ y)
    (h_fresh : Γ.lookup x = none) :
    EnvEvalClosed' ((x, v) :: Γ) := by
  intro y w h_lookup z h_z_free
  simp only [Env.lookup] at h_lookup
  simp only [isNeutral, Env.lookup]
  split at h_lookup <;> rename_i h_eq
  · -- y = x: w = v
    cases h_lookup
    have h_z := h_v z h_z_free
    simp only [isNeutral, Env.lookup] at h_z
    split
    · -- z = x: but evalFreeVars(v) only contains neutral vars from Γ,
      -- and x is fresh (not in Γ), so x can't be neutral in Γ.
      -- Therefore z = x is impossible.
      rename_i h_zx
      have h_xz : x = z := beq_iff_eq.mp h_zx
      rw [← h_xz] at h_z
      exact absurd h_z (by rw [h_fresh]; simp)
    · exact h_z
  · -- y ≠ x: w from Γ
    have h_z := h y w h_lookup z h_z_free
    simp only [isNeutral, Env.lookup] at h_z
    split
    · -- z = x: z is neutral in Γ means Γ.lookup z = some (var z).
      -- But z = x and Γ.lookup x = none. Contradiction.
      rename_i h_zx
      have h_xz : x = z := beq_iff_eq.mp h_zx
      rw [← h_xz] at h_z
      exact absurd h_z (by rw [h_fresh]; simp)
    · exact h_z

/-- **General coverage: absEval outputs have evalFreeVars ⊆ P for any predicate P
    that is closed under env lookups.**

    This is the key generalization that avoids the EnvEvalClosed' shadowing issue.
    By parameterizing over an arbitrary predicate P (rather than neutralVars(Γ)):
    - The lam/iota cases temporarily expand P to include the binder name
    - The app-lam case reuses P unchanged (IH on a guarantees τ_a's evalFreeVars ∈ P)
    - No need for EnvEvalClosed' on extended envs, avoiding the shadowing problem

    The original `absEval_evalFreeVars_neutral` follows as a corollary with
    P = isNeutral Γ. -/
theorem absEval_evalFreeVars_general
    (fuel : Nat) (Γ : Env) (e τ : Expr)
    (P : Name → Prop)
    (h_eval : absEval fuel Γ e = some τ)
    (h_env : ∀ x v, Γ.lookup x = some v → ∀ y, y ∈ v.evalFreeVars → P y)
    : ∀ y, y ∈ τ.evalFreeVars → P y := by
  induction fuel generalizing Γ e τ P with
  | zero => simp [absEval] at h_eval
  | succ n ih =>
    cases e with
    | var x =>
      simp only [absEval] at h_eval
      exact h_env x τ h_eval
    | type =>
      simp only [absEval] at h_eval; cases h_eval
      intro y hy; simp [Expr.evalFreeVars] at hy
    | asc _term ty =>
      simp only [absEval] at h_eval
      exact ih Γ ty τ P h_eval h_env
    | fix inner =>
      simp only [absEval] at h_eval
      cases inner with
      | lam _f dom _body =>
        exact ih Γ dom τ P h_eval h_env
      | _ => simp [absEval] at h_eval
    | lam x _dom body =>
      simp only [absEval] at h_eval
      cases hb : absEval n ((x, .var x) :: Γ) body with
      | none => simp [hb] at h_eval
      | some body' =>
        simp [hb] at h_eval; cases h_eval
        -- τ = lam x _dom body', evalFreeVars = body'.evalFreeVars.filter(·≠x)
        intro y hy
        -- hy : y ∈ (lam x _dom body').evalFreeVars = body'.evalFreeVars.filter(·!=x)
        have ⟨h_mem, h_ne⟩ := List.mem_filter.mp hy
        -- IH on body with predicate P' = fun z => P z ∨ z = x
        have h_env' : ∀ z v, Env.lookup ((x, .var x) :: Γ) z = some v →
            ∀ w, w ∈ v.evalFreeVars → P w ∨ w = x := by
          intro z v h_lookup w hw
          simp only [Env.lookup] at h_lookup
          split at h_lookup <;> rename_i h_eq
          · cases h_lookup; simp [Expr.evalFreeVars] at hw; exact Or.inr hw
          · exact Or.inl (h_env z v h_lookup w hw)
        have ih_body := ih ((x, .var x) :: Γ) body body' (fun z => P z ∨ z = x) hb h_env' y h_mem
        cases ih_body with
        | inl h => exact h
        | inr h =>
          -- y = x but filter says y ≠ x: contradiction
          exfalso
          have h_ne' : ¬(y == x) = true := by
            intro heq; rw [beq_iff_eq.mp heq] at h_ne; simp at h_ne
          exact h_ne' (beq_iff_eq.mpr h)
    | iota x body =>
      simp only [absEval] at h_eval
      cases hb : absEval n ((x, .var x) :: Γ) body with
      | none => simp [hb] at h_eval
      | some body' =>
        simp [hb] at h_eval; cases h_eval
        -- τ = iota x body', evalFreeVars = body'.evalFreeVars.filter(·≠x)
        intro y hy
        have ⟨h_mem, h_ne⟩ := List.mem_filter.mp hy
        have h_env' : ∀ z v, Env.lookup ((x, .var x) :: Γ) z = some v →
            ∀ w, w ∈ v.evalFreeVars → P w ∨ w = x := by
          intro z v h_lookup w hw
          simp only [Env.lookup] at h_lookup
          split at h_lookup <;> rename_i h_eq
          · cases h_lookup; simp [Expr.evalFreeVars] at hw; exact Or.inr hw
          · exact Or.inl (h_env z v h_lookup w hw)
        have ih_body := ih ((x, .var x) :: Γ) body body' (fun z => P z ∨ z = x) hb h_env' y h_mem
        cases ih_body with
        | inl h => exact h
        | inr h =>
          exfalso
          have h_ne' : ¬(y == x) = true := by
            intro heq; rw [beq_iff_eq.mp heq] at h_ne; simp at h_ne
          exact h_ne' (beq_iff_eq.mpr h)
    | app f a =>
      simp only [absEval] at h_eval
      cases hf : absEval n Γ f with
      | none => simp [hf] at h_eval
      | some τ_f =>
        cases ha : absEval n Γ a with
        | none => simp [hf, ha] at h_eval
        | some τ_a =>
          rw [hf, ha] at h_eval
          have ih_f := ih Γ f τ_f P hf h_env
          have ih_a := ih Γ a τ_a P ha h_env
          cases τ_f with
          | lam x _dom body =>
            -- Beta reduction: τ = absEval n ((x, τ_a) :: Γ) body
            simp only at h_eval
            have h_env' : ∀ z v, Env.lookup ((x, τ_a) :: Γ) z = some v →
                ∀ w, w ∈ v.evalFreeVars → P w := by
              intro z v h_lookup w hw
              simp only [Env.lookup] at h_lookup
              split at h_lookup <;> rename_i h_eq
              · cases h_lookup; exact ih_a w hw
              · exact h_env z v h_lookup w hw
            exact ih ((x, τ_a) :: Γ) body τ P h_eval h_env'
          | type =>
            simp only at h_eval; cases h_eval
            intro y hy; simp [Expr.evalFreeVars] at hy
          | var _ | app _ _ | asc _ _ | fix _ | iota _ _ =>
            -- Stuck: result is app τ_f τ_a
            simp only at h_eval; cases h_eval
            intro y hy
            -- evalFreeVars(.app τ_f τ_a) = τ_f.evalFreeVars ++ τ_a.evalFreeVars (by defn)
            rcases List.mem_append.mp hy with h1 | h2
            · exact ih_f y h1
            · exact ih_a y h2

/-- **absEval outputs have evalFreeVars ⊆ neutralVars(Γ).**

    Corollary of `absEval_evalFreeVars_general` with P = isNeutral Γ.
    The EnvEvalClosed' precondition says exactly that the env values'
    evalFreeVars are neutral, which is the closure condition for P. -/
theorem absEval_evalFreeVars_neutral
    (fuel : Nat) (Γ : Env) (e τ : Expr)
    (h_eval : absEval fuel Γ e = some τ)
    (h_env : EnvEvalClosed' Γ)
    : ∀ y, y ∈ τ.evalFreeVars → isNeutral Γ y :=
  absEval_evalFreeVars_general fuel Γ e τ (isNeutral Γ) h_eval h_env
