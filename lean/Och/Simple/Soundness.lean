import Och.Simple.Syntax
import Och.Simple.Subtype
import Och.Simple.Eval
import Och.Simple.Properties

/-!
# Semantic Substitution (Soundness Part 1)

Proves: if `Γ ⊢ e ⊑ τ` and `γ` is compatible with `Γ`, then
`[] ⊢ closingSubst γ e ⊑ closingSubst γ τ`.

The key insight is defining Compatible so each value is related to its type
*in the remaining context* rather than at empty context.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

-- ============================================================
-- Closing substitution
-- ============================================================

/-- Apply a list of closed values as a closing substitution.
    If `γ = [v₀, v₁, v₂, ...]`, then `closingSubst γ e` replaces
    `var 0 → v₀`, `var 1 → v₁`, etc. -/
def closingSubst : List Expr → Expr → Expr
  | [], e => e
  | v :: rest, e => closingSubst rest (e.subst 0 v)

-- ============================================================
-- closingSubst lemmas
-- ============================================================

/-- Top is closed under any substitution. -/
theorem closingSubst_top : (γ : List Expr) → closingSubst γ .top = .top
  | [] => rfl
  | _ :: rest => by
    show closingSubst rest (Expr.subst .top 0 _) = .top
    simp [Expr.subst]
    exact closingSubst_top rest

/-- closingSubst distributes over app. -/
theorem closingSubst_app : (γ : List Expr) → (f a : Expr) →
    closingSubst γ (.app f a) = .app (closingSubst γ f) (closingSubst γ a)
  | [], _, _ => rfl
  | v :: rest, f, a => by
    show closingSubst rest (Expr.subst (.app f a) 0 v) = _
    unfold Expr.subst
    exact closingSubst_app rest (f.subst 0 v) (a.subst 0 v)

/-- closingSubst distributes over asc. -/
theorem closingSubst_asc : (γ : List Expr) → (e τ : Expr) →
    closingSubst γ (.asc e τ) = .asc (closingSubst γ e) (closingSubst γ τ)
  | [], _, _ => rfl
  | v :: rest, e, τ => by
    show closingSubst rest (Expr.subst (.asc e τ) 0 v) = _
    unfold Expr.subst
    exact closingSubst_asc rest (e.subst 0 v) (τ.subst 0 v)

/-- closingSubst preserves the lam constructor. -/
theorem closingSubst_lam_is_lam : (γ : List Expr) → (D body : Expr) →
    ∃ D' body', closingSubst γ (.lam D body) = .lam D' body'
  | [], D, body => ⟨D, body, rfl⟩
  | v :: rest, D, body => by
    show ∃ D' body', closingSubst rest ((Expr.lam D body).subst 0 v) = .lam D' body'
    simp only [Expr.subst]
    exact closingSubst_lam_is_lam rest (D.subst 0 v) (body.subst 1 (v.shift 0 1))

-- ============================================================
-- Compatibility (γ ⊨ Γ)
-- ============================================================

/-- A closing substitution `γ` is compatible with context `Γ` if each value
    is Sub-related to its type in the remaining context. -/
inductive Compatible : List Expr → Ctx → Type where
  | nil : Compatible [] []
  | cons {v : Expr} {T : Expr} {γ : List Expr} {Γ : Ctx} :
      Compatible γ Γ →
      Sub Γ v T →
      Compatible (v :: γ) (T :: Γ)

-- ============================================================
-- Semantic substitution theorem
-- ============================================================

/-- **Semantic substitution**: If `Γ ⊢ e ⊑ τ` and `γ` is compatible with `Γ`,
    then `[] ⊢ closingSubst γ e ⊑ closingSubst γ τ`. -/
noncomputable def semanticSubst {Γ : Ctx} {e τ : Expr} {γ : List Expr}
    (hsub : Sub Γ e τ)
    (hcompat : Compatible γ Γ)
    : Sub [] (closingSubst γ e) (closingSubst γ τ) := by
  induction hcompat generalizing e τ with
  | nil =>
    exact hsub
  | @cons v T γ' Γ' hcompat' hv ih =>
    show Sub [] (closingSubst γ' (e.subst 0 v)) (closingSubst γ' (τ.subst 0 v))
    exact ih (Sub.subst_lemma hsub hv)

-- ============================================================
-- Eval preservation (Soundness Part 2)
-- ============================================================

-- Helper: eval of a lambda returns itself
theorem eval_lam (fuel : Nat) (D body : Expr) (h : fuel > 0) :
    eval fuel (.lam D body) = some (.lam D body) := by
  cases fuel with
  | zero => omega
  | succ n => simp [eval]

-- Helper: eval of top returns itself
theorem eval_top (fuel : Nat) (h : fuel > 0) :
    eval fuel .top = some .top := by
  cases fuel with
  | zero => omega
  | succ n => simp [eval]

-- Helper: eval of var returns itself
theorem eval_var (fuel : Nat) (k : Nat) (h : fuel > 0) :
    eval fuel (.var k) = some (.var k) := by
  cases fuel with
  | zero => omega
  | succ n => simp [eval]

-- Helper: eval of asc erases the ascription
theorem eval_asc_decompose {fuel : Nat} {e ty v : Expr}
    (he : eval (fuel + 1) (.asc e ty) = some v) :
    eval fuel e = some v := by
  simp [eval] at he; exact he

-- Fuel monotonicity: if eval succeeds at fuel n, it succeeds at fuel n+k with the same result
theorem eval_mono (e : Expr) (fuel : Nat) (v : Expr)
    (h : eval fuel e = some v) (k : Nat) :
    eval (fuel + k) e = some v := by
  induction fuel generalizing e v k with
  | zero => simp [eval] at h
  | succ n ih =>
    have hrw : n + 1 + k = (n + k) + 1 := by omega
    cases e with
    | var m =>
      simp [eval] at h; subst h
      rw [hrw]; simp [eval]
    | top =>
      simp [eval] at h; subst h
      rw [hrw]; simp [eval]
    | lam dom body =>
      simp [eval] at h; subst h
      rw [hrw]; simp [eval]
    | asc e ty =>
      have h' : eval n e = some v := by simp [eval] at h; exact h
      have := ih e v h' k
      rw [hrw]; simp [eval]; exact this
    | app f a =>
      simp [eval, bind, Option.bind] at h
      cases hf : eval n f with
      | none => simp [hf] at h
      | some f' =>
        cases ha : eval n a with
        | none => simp [hf, ha] at h
        | some a' =>
          simp [hf, ha] at h
          have hf' := ih f f' hf k
          have ha' := ih a a' ha k
          rw [hrw]; simp [eval, bind, Option.bind, hf', ha']
          match hm : f' with
          | .lam dom body =>
            simp [hm] at h; simp; exact ih (body.subst 0 a') v h k
          | .var k' => simp [hm] at h ⊢; exact h
          | .top => simp [hm] at h ⊢; exact h
          | .app g b => simp [hm] at h ⊢; exact h
          | .asc e' t' => simp [hm] at h ⊢; exact h

-- eval results satisfy the Value predicate
theorem eval_produces_value {fuel : Nat} {e v : Expr}
    (h : eval fuel e = some v) : Value v := by
  induction fuel generalizing e v with
  | zero => simp [eval] at h
  | succ n ih =>
    cases e with
    | var k => simp [eval] at h; subst h; exact Value.var k
    | top => simp [eval] at h; subst h; exact Value.top
    | lam D body => simp [eval] at h; subst h; exact Value.lam D body
    | asc e ty => simp [eval] at h; exact ih h
    | app f a =>
      simp [eval, bind, Option.bind] at h
      cases hf : eval n f with
      | none => simp [hf] at h
      | some f' =>
        cases ha : eval n a with
        | none => simp [hf, ha] at h
        | some a' =>
          simp [hf, ha] at h
          match hm : f' with
          | .lam dom body => simp [hm] at h; exact ih h
          | .var k =>
            simp [hm] at h; subst h
            exact Value.stuckApp (.var k) a' (by intro ⟨d, b, h⟩; exact Expr.noConfusion h)
          | .top =>
            simp [hm] at h; subst h
            exact Value.stuckApp .top a' (by intro ⟨d, b, h⟩; exact Expr.noConfusion h)
          | .app g b =>
            simp [hm] at h; subst h
            exact Value.stuckApp (.app g b) a' (by intro ⟨d, b', h⟩; exact Expr.noConfusion h)
          | .asc e' t' =>
            simp [hm] at h; subst h
            exact Value.stuckApp (.asc e' t') a' (by intro ⟨d, b', h⟩; exact Expr.noConfusion h)

-- Inversion: Sub Γ (lam A b₁) (lam B b₂) implies Sub Γ B A and Sub (B :: Γ) b₁ b₂
noncomputable def sub_lam_inv {Γ : Ctx} {A B b₁ b₂ : Expr}
    (h : Sub Γ (.lam A b₁) (.lam B b₂)) : Sub Γ B A × Sub (B :: Γ) b₁ b₂ := by
  cases h with
  | refl =>
    exact ⟨Sub.refl _ _, Sub.refl _ _⟩
  | lam _ _ _ _ _ hBA hbody =>
    exact ⟨hBA, hbody⟩

-- ============================================================
-- Eval preservation
-- ============================================================

/-- **Eval preservation**: If `[] ⊢ e ⊑ τ` and both `e` and `τ` evaluate to
    values `v_e` and `v_τ`, then `[] ⊢ v_e ⊑ v_τ`.

    Proved by induction on the Sub derivation. All cases are handled except
    [App], which requires connecting the typing-level beta reduction
    (R.subst 0 a) with the evaluator-level beta reduction (body.subst 0 a'). -/
noncomputable def evalPreservation {e τ : Expr}
    (hsub : Sub [] e τ) (fuel : Nat) (v_e v_τ : Expr)
    (he : eval fuel e = some v_e) (hτ : eval fuel τ = some v_τ)
    : Sub [] v_e v_τ := by
  -- We can't do `induction hsub` directly because the context is fixed at [].
  -- Instead, we generalize e and τ and do cases on hsub.
  -- Actually, let's just do cases — hsub is a Sub [] e τ, we case-split on the rule.
  cases hsub with
  | refl _ a =>
    -- e = τ = a, so v_e = v_τ
    rw [he] at hτ; cases hτ
    exact Sub.refl [] v_e
  | top _ a =>
    -- τ = top
    cases fuel with
    | zero => simp [eval] at hτ
    | succ n =>
      simp [eval] at hτ; subst hτ
      exact Sub.top [] v_e
  | var _ x _ _ hget _ =>
    -- Impossible: empty context has no bindings
    simp [Ctx.get?, List.get?] at hget
  | lam _ A B b₁ b₂ hBA hbody =>
    -- e = lam A b₁, τ = lam B b₂
    -- Both evaluate to themselves (at fuel > 0)
    cases fuel with
    | zero => simp [eval] at he
    | succ n =>
      simp [eval] at he hτ
      subst he; subst hτ
      exact Sub.lam [] A B b₁ b₂ hBA hbody
  | ascL _ e' τ' b he'τ' hτ'b =>
    -- e = asc e' τ', eval strips ascription
    cases fuel with
    | zero => simp [eval] at he
    | succ n =>
      simp [eval] at he
      -- he : eval n e' = some v_e
      -- Use transitivity: Sub [] e' b, then recurse
      have he' : eval (n + 1) e' = some v_e := eval_mono e' n v_e he 1
      exact evalPreservation (Sub.trans he'τ' hτ'b) (n + 1) v_e v_τ he' hτ
  | ascR _ a e' τ' he'τ' hae' =>
    -- τ = asc e' τ', eval strips ascription
    cases fuel with
    | zero => simp [eval] at hτ
    | succ n =>
      simp [eval] at hτ
      -- hτ : eval n e' = some v_τ
      have hτ' : eval (n + 1) e' = some v_τ := eval_mono e' n v_τ hτ 1
      exact evalPreservation hae' (n + 1) v_e v_τ he hτ'
  | app _ f a b D R hfD haD hRb =>
    -- e = app f a, τ = b
    -- Decompose the eval of (app f a)
    cases fuel with
    | zero => simp [eval] at he
    | succ n =>
      simp [eval, bind, Option.bind] at he
      cases hf_eval : eval n f with
      | none => simp [hf_eval] at he
      | some f' =>
        cases ha_eval : eval n a with
        | none => simp [hf_eval, ha_eval] at he
        | some a' =>
          simp [hf_eval, ha_eval] at he
          -- n > 0 because eval n f = some f' (eval 0 always returns none)
          have hn_pos : n > 0 := by
            cases n with
            | zero => simp [eval] at hf_eval
            | succ m => omega
          -- By evalPreservation on f: Sub [] f' (lam D R)
          -- (lam D R is already a value, evals to itself)
          have hf_lam_eval : eval n (.lam D R) = some (.lam D R) :=
            eval_lam n D R hn_pos
          have hf_sub : Sub [] f' (.lam D R) :=
            evalPreservation hfD n f' (.lam D R) hf_eval hf_lam_eval
          -- Case split on f'
          cases f' with
          | lam D₁ body₁ =>
            simp at he
            -- he : eval n (body₁.subst 0 a') = some v_e
            -- hf_sub : Sub [] (lam D₁ body₁) (lam D R)
            -- By lambda inversion: Sub [] D D₁ and Sub [D] body₁ R
            have ⟨hDD₁, hbody₁R⟩ := sub_lam_inv hf_sub
            -- What we CAN derive:
            --   Sub [D] body₁ R     (from lam_inv)
            --   Sub [] a D          (given as haD)
            --   Sub.subst_lemma hbody₁R haD : Sub [] (body₁.subst 0 a) (R.subst 0 a)
            --   Sub.trans (above) hRb : Sub [] (body₁.subst 0 a) b
            --
            -- What the evaluator computed:
            --   eval n (body₁.subst 0 a') = some v_e   (where a' = eval n a)
            --   eval (n+1) b = some v_τ
            --
            -- THE GAP: We have Sub [] (body₁.subst 0 a) b, but the evaluator
            -- beta-reduced with a' (the evaluated form of a), not a itself.
            -- To close this case we need one of:
            --   (A) An "eval-subst commutation" lemma showing
            --       eval(body.subst 0 a') = eval(body.subst 0 a) when eval a = a'.
            --       This is a standard CBV property but requires a non-trivial proof
            --       by induction on eval, showing that pre-evaluating the substituted
            --       term doesn't change the final result.
            --   (B) Sub [] a' D (so subst_lemma gives Sub [] (body₁.subst 0 a') (R.subst 0 a'))
            --       PLUS a way to connect R.subst 0 a' back to b (which is typed via R.subst 0 a).
            --       This still needs eval-subst commutation for the R.subst 0 a' ⊑ b step.
            sorry
          | var k =>
            -- f' = var k, stuck app: v_e = app (var k) a'
            simp at he; subst he
            -- hf_sub : Sub [] (var k) (lam D R) — contradiction at empty context
            -- Only possible constructor is [Var] which requires non-empty context
            cases hf_sub with
            | var _ _ _ _ hget _ => simp [Ctx.get?, List.get?] at hget
          | top =>
            -- f' = top, stuck app: v_e = app top a'
            simp at he; subst he
            -- hf_sub : Sub [] top (lam D R) — no constructor applies
            exact nomatch hf_sub
          | app g c =>
            -- f' = app g c (stuck application)
            simp at he; subst he
            -- hf_sub : Sub [] (app g c) (lam D R) is possible via [App] rule.
            -- v_e = app (app g c) a'
            -- Same fundamental difficulty as the lam case, compounded by stuck app.
            sorry
          | asc e' t' =>
            -- eval never returns an ascription — contradiction
            -- Value only has constructors for top, lam, var, stuckApp (app _ _)
            exact nomatch (eval_produces_value hf_eval)

end Och.Simple
