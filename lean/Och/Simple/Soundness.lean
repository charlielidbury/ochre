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
@[simp] theorem closingSubst_top : (γ : List Expr) → closingSubst γ .top = .top
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
    | mu ann body =>
      have h' : eval n (body.subst 0 (.mu ann body)) = some v := by simp [eval] at h; exact h
      have := ih _ v h' k
      rw [hrw]; simp [eval]; exact this
    | app f a =>
      simp [eval, bind, Option.bind] at h
      cases hf : eval n f with
      | none => simp [hf] at h
      | some f' =>
        simp [hf] at h
        have hf' := ih f f' hf k
        rw [hrw]; simp [eval, bind, Option.bind, hf']
        match hm : f' with
        | .lam dom body =>
          simp [hm] at h; simp; exact ih (body.subst 0 a) v h k
        | .var k' => simp [hm] at h ⊢; exact h
        | .top => simp [hm] at h ⊢; exact h
        | .app g b => simp [hm] at h ⊢; exact h
        | .asc e' t' => simp [hm] at h ⊢; exact h
        | .mu ann' body' => simp [hm] at h ⊢; exact h

-- eval results satisfy the Value predicate
-- (Note: with lazy evaluation, stuck apps contain unevaluated arguments,
--  so we don't assert Value for the argument.)
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
    | mu ann body => simp [eval] at h; exact ih h
    | app f a =>
      simp [eval, bind, Option.bind] at h
      cases hf : eval n f with
      | none => simp [hf] at h
      | some f' =>
        simp [hf] at h
        match hm : f' with
        | .lam dom body => simp [hm] at h; exact ih h
        | .var k =>
          simp [hm] at h; subst h
          exact Value.stuckApp (.var k) a (by intro ⟨d, b, h⟩; exact Expr.noConfusion h)
        | .top =>
          simp [hm] at h; subst h
          exact Value.stuckApp .top a (by intro ⟨d, b, h⟩; exact Expr.noConfusion h)
        | .app g b =>
          simp [hm] at h; subst h
          exact Value.stuckApp (.app g b) a (by intro ⟨d, b', h⟩; exact Expr.noConfusion h)
        | .asc e' t' =>
          simp [hm] at h; subst h
          exact Value.stuckApp (.asc e' t') a (by intro ⟨d, b', h⟩; exact Expr.noConfusion h)
        | .mu ann body =>
          simp [hm] at h; subst h
          exact Value.stuckApp (.mu ann body) a (by intro ⟨d, b', h⟩; exact Expr.noConfusion h)

-- Inversion: Sub Γ (lam A b₁) (lam B b₂) implies Sub Γ B A and Sub (B :: Γ) b₁ b₂
noncomputable def sub_lam_inv {Γ : Ctx} {A B b₁ b₂ : Expr}
    (h : Sub Γ (.lam A b₁) (.lam B b₂)) : Sub Γ B A × Sub (B :: Γ) b₁ b₂ := by
  cases h with
  | refl =>
    exact ⟨Sub.refl _ _, Sub.refl _ _⟩
  | lam _ _ _ _ _ hBA hbody =>
    exact ⟨hBA, hbody⟩

-- Fuel monotonicity (≤ version): if eval succeeds at fuel n, it succeeds at any fuel m ≥ n
theorem eval_mono_le (e : Expr) (n m : Nat) (v : Expr)
    (h : eval n e = some v) (hle : n ≤ m) :
    eval m e = some v := by
  have ⟨k, hk⟩ := Nat.le.dest hle
  rw [← hk]; exact eval_mono e n v h k

-- If eval fuel e = some v, then fuel ≥ 1
theorem eval_pos {fuel : Nat} {e v : Expr} (h : eval fuel e = some v) : fuel ≥ 1 := by
  cases fuel with
  | zero => simp [eval] at h
  | succ n => omega

-- Idempotency: if eval n e = some v, then eval n v = some v.
-- Values re-evaluate to themselves at the same fuel.
theorem eval_idempotent {fuel : Nat} {e v : Expr}
    (h : eval fuel e = some v) : eval fuel v = some v := by
  induction fuel generalizing e v with
  | zero => simp [eval] at h
  | succ n ih =>
    cases e with
    | var k => simp [eval] at h; subst h; simp [eval]
    | top => simp [eval] at h; subst h; simp [eval]
    | lam D body => simp [eval] at h; subst h; simp [eval]
    | asc e ty =>
      simp [eval] at h
      have hv := ih h
      exact eval_mono v n v hv 1
    | mu ann body =>
      simp [eval] at h
      have hv := ih h
      exact eval_mono v n v hv 1
    | app f a =>
      simp [eval, bind, Option.bind] at h
      cases hf : eval n f with
      | none => simp [hf] at h
      | some f' =>
        simp [hf] at h
        match hm : f' with
        | .lam dom body =>
          simp [hm] at h
          exact eval_mono v n v (ih h) 1
        | .var k =>
          simp [hm] at h; subst h
          simp [eval, bind, Option.bind, eval_var n k (eval_pos hf)]
        | .top =>
          simp [hm] at h; subst h
          simp [eval, bind, Option.bind, eval_top n (eval_pos hf)]
        | .app g b =>
          simp [hm] at h; subst h
          simp [eval, bind, Option.bind, ih hf]
        | .asc e' t' =>
          simp [hm] at h; subst h; exact nomatch (eval_produces_value hf)
        | .mu ann' body' =>
          simp [hm] at h; subst h; exact nomatch (eval_produces_value hf)

-- An expression is an "eval result" if some eval produced it.
def IsEvalResult (v : Expr) : Prop := ∃ n e, eval n e = some v

-- eval results are eval results (tautological but useful)
theorem eval_is_eval_result {n : Nat} {e v : Expr} (h : eval n e = some v) :
    IsEvalResult v := ⟨n, e, h⟩

-- If eval produces an app (f a), then f is an eval result and not a lam.
theorem eval_app_head_result {n : Nat} {e f a : Expr}
    (h : eval n e = some (.app f a)) :
    IsEvalResult f ∧ (¬ ∃ d b, f = .lam d b) := by
  induction n generalizing e with
  | zero => simp [eval] at h
  | succ n ih =>
    cases e with
    | var k => simp [eval] at h
    | top => simp [eval] at h
    | lam D body => simp [eval] at h
    | asc e ty =>
      simp [eval] at h; exact ih h
    | mu ann body =>
      simp [eval] at h; exact ih h
    | app f' a' =>
      simp [eval, bind, Option.bind] at h
      cases hf : eval n f' with
      | none => simp [hf] at h
      | some f'' =>
        simp [hf] at h
        match hm : f'' with
        | .lam dom body =>
          simp [hm] at h; exact ih h
        | .var k | .top | .app g c =>
          simp [hm] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨⟨n, f', hf⟩, by intro ⟨d, b, h⟩; exact Expr.noConfusion h⟩
        | .asc e' t' =>
          subst hm; exact nomatch (eval_produces_value hf)
        | .mu ann body =>
          subst hm; exact nomatch (eval_produces_value hf)

-- Key lemma: Sub [] v (lam D R) where v is an eval result implies v is a lam.
-- Auxiliary with size bound, proved by recursion on bound.
-- Returns False instead of ∃ to avoid Prop-elimination issues
private noncomputable def eval_result_sub_lam_not_app :
    (bound : Nat) → {f a D R : Expr} → (hsub : Sub [] (.app f a) (.lam D R)) →
    IsEvalResult (.app f a) → hsub.size ≤ bound → False
  | 0 => fun hsub _ hle => absurd hle (by have := hsub.size_pos; omega)
  | bound + 1 => fun hsub heval hle => by
    cases hsub with
    | @app _ f_head a_arg _ D' R' hfD' _ _ =>
      obtain ⟨n, e, he⟩ := heval
      obtain ⟨hf_eval, hf_not_lam⟩ := eval_app_head_result he
      cases hfD' with
      | refl => exact absurd ⟨D', R', rfl⟩ hf_not_lam
      | lam _ _ _ _ _ _ _ => exact absurd ⟨_, _, rfl⟩ hf_not_lam
      | var _ _ _ _ hget _ => simp [Ctx.get?, List.get?] at hget
      | ascL _ _ _ _ _ _ =>
        obtain ⟨n', e', he'⟩ := hf_eval; exact nomatch (eval_produces_value he')
      | mu _ _ _ _ _ _ =>
        obtain ⟨n', e', he'⟩ := hf_eval; exact nomatch (eval_produces_value he')
      | muUnfoldL _ _ _ _ _ =>
        -- muUnfoldL requires f to be `mu A body`, but hf_eval tells us
        -- `eval n' e = some f`, and eval never produces a mu as a value.
        obtain ⟨n', e', he'⟩ := hf_eval; exact nomatch (eval_produces_value he')
      | @app _ g c _ D'' R'' hgD'' hcD'' hR''D' =>
        rename_i haD_inner hRb_inner
        let rebuilt := Sub.app [] g c (.lam D' R') D'' R'' hgD'' hcD'' hR''D'
        suffices h : rebuilt.size ≤ bound from
          eval_result_sub_lam_not_app bound rebuilt hf_eval h
        show 1 + hgD''.size + hcD''.size + hR''D'.size ≤ bound
        simp [Sub.size] at hle; omega

-- Wrapper: Sub [] (app f a) (lam D R) with eval result is impossible
noncomputable def eval_result_sub_lam_app_absurd
    {f a D R : Expr} (hsub : Sub [] (.app f a) (.lam D R))
    (heval : IsEvalResult (.app f a)) : False :=
  eval_result_sub_lam_not_app hsub.size hsub heval (Nat.le_refl _)

-- ============================================================
-- Eval preservation
-- ============================================================

/-- Inner recursive helper: takes a bound `n` and proves the theorem for
    any `fuel + fuel_τ ≤ n`. -/
private noncomputable def evalPreservation_aux :
    (n : Nat) →
    (∀ (e τ : Expr) (_ : Sub [] e τ) (fuel fuel_τ : Nat) (v_e v_τ : Expr),
      fuel + fuel_τ ≤ n →
      eval fuel e = some v_e → eval fuel_τ τ = some v_τ → Sub [] v_e v_τ)
  | 0 => fun _ _ _ fuel _ _ _ hbound he _ => by
    have : fuel = 0 := by omega
    subst this; simp [eval] at he
  | n + 1 => fun e τ hsub fuel fuel_τ v_e v_τ hbound he hτ => by
    let ih := evalPreservation_aux n
    cases hsub with
    | refl =>
      -- e = τ. Use eval_mono to align fuels.
      if hle_fuel : fuel ≤ fuel_τ then
        have h_align := eval_mono_le _ fuel fuel_τ v_e he hle_fuel
        rw [h_align] at hτ; cases hτ; exact Sub.refl [] v_e
      else
        have hle' : fuel_τ ≤ fuel := by omega
        have h_align := eval_mono_le _ fuel_τ fuel v_τ hτ hle'
        rw [he] at h_align; cases h_align; exact Sub.refl [] v_e

    | top _ a =>
      -- τ = ⊤
      have hpos : fuel_τ ≥ 1 := eval_pos hτ
      have : eval fuel_τ .top = some .top := eval_top fuel_τ hpos
      rw [this] at hτ; cases hτ
      exact Sub.top [] v_e

    | var _ x _ _ hget _ =>
      simp [Ctx.get?, List.get?] at hget

    | lam _ A B b₁ b₂ hBA hbody =>
      have hpos_e : fuel ≥ 1 := eval_pos he
      have hpos_τ : fuel_τ ≥ 1 := eval_pos hτ
      have he' : eval fuel (.lam A b₁) = some (.lam A b₁) := eval_lam fuel A b₁ hpos_e
      have hτ' : eval fuel_τ (.lam B b₂) = some (.lam B b₂) := eval_lam fuel_τ B b₂ hpos_τ
      rw [he'] at he; cases he
      rw [hτ'] at hτ; cases hτ
      exact Sub.lam [] A B b₁ b₂ hBA hbody

    | ascL _ _ _ _ heτ hτb =>
      -- e = asc e' τ'. eval strips ascription.
      cases fuel with
      | zero => simp [eval] at he
      | succ m =>
        simp [eval] at he
        exact ih _ _ (Sub.trans heτ hτb) m fuel_τ _ _ (by omega) he hτ

    | ascR _ _ _ _ _ hae =>
      -- τ = asc e' τ'. eval strips ascription.
      cases fuel_τ with
      | zero => simp [eval] at hτ
      | succ m =>
        simp [eval] at hτ
        exact ih _ _ hae fuel m _ _ (by omega) he hτ

    | mu _ A b _ hAc hbA =>
      cases fuel with
      | zero => simp [eval] at he
      | succ m =>
        simp [eval] at he
        -- Unfold mu: derive Sub [] (b.subst 0 (mu A b)) c via mu-A-trans chain
        have hmuA : Sub [] (.mu A b) A := Sub.mu [] A b A (Sub.refl [] A) hbA
        have hbody_sub : Sub [] (b.subst 0 (.mu A b)) A := by
          have h1 := Sub.subst_lemma hbA hmuA; rw [Expr.subst_shift_cancel_zero] at h1; exact h1
        exact ih _ _ (Sub.trans hbody_sub hAc) m fuel_τ _ _ (by omega) he hτ

    | app _ f a _ D R hfD haD hRb =>
      cases fuel with
      | zero => simp [eval] at he
      | succ m =>
        simp [eval, bind, Option.bind] at he
        cases hf_eval : eval m f with
        | none => simp [hf_eval] at he
        | some f' =>
          simp [hf_eval] at he
          match hm_f : f' with
          | .lam D₁ body₁ =>
            simp [hm_f] at he
            have hm_pos : m ≥ 1 := eval_pos hf_eval
            have hfuel_τ_pos : fuel_τ ≥ 1 := eval_pos hτ
            have hlam_eval1 : eval 1 (.lam D R) = some (.lam D R) := eval_lam 1 D R (by omega)
            have hf_sub : Sub [] (.lam D₁ body₁) (.lam D R) :=
              ih _ _ hfD m 1 _ _ (by omega) hf_eval hlam_eval1
            have ⟨hDD₁, hbody₁R⟩ := sub_lam_inv hf_sub
            have hsubst : Sub [] (body₁.subst 0 a) (R.subst 0 a) :=
              Sub.subst_lemma hbody₁R haD
            have hsub_body := Sub.trans hsubst hRb
            exact ih _ _ hsub_body m fuel_τ _ _ (by omega) he hτ

          | .var k =>
            simp [hm_f] at he; subst he
            have _ : fuel_τ ≥ 1 := eval_pos hτ
            have hf_sub := ih _ _ hfD m 1 _ _ (by omega) hf_eval (eval_lam 1 D R (by omega))
            cases hf_sub with | var _ _ _ _ hget _ => simp [Ctx.get?, List.get?] at hget
          | .top =>
            simp [hm_f] at he; subst he
            have _ : fuel_τ ≥ 1 := eval_pos hτ
            exact nomatch ih _ _ hfD m 1 _ _ (by omega) hf_eval (eval_lam 1 D R (by omega))
          | .app g c =>
            simp [hm_f] at he; subst he
            have _ : fuel_τ ≥ 1 := eval_pos hτ
            have hf_sub := ih _ _ hfD m 1 _ _ (by omega) hf_eval (eval_lam 1 D R (by omega))
            exact (eval_result_sub_lam_app_absurd hf_sub ⟨m, _, hf_eval⟩).elim
          | .asc e' t' => exact nomatch (eval_produces_value hf_eval)
          | .mu ann body => exact nomatch (eval_produces_value hf_eval)

    | muUnfoldL _ A body _ hBody =>
      -- e = mu A body. eval unfolds one step to body.subst 0 (mu A body).
      -- hBody : Sub [] (body.subst 0 (mu A body)) τ, so recurse.
      cases fuel with
      | zero => simp [eval] at he
      | succ m =>
        simp [eval] at he
        exact ih _ _ hBody m fuel_τ _ _ (by omega) he hτ

    | muR _ _ A body hA hBody =>
      -- τ = mu A body. CYCLE DETECTION SORRY:
      -- We have hA : Sub [] e A and hBody : Sub [] e (body.subst 0 e).
      -- eval on τ (a mu) unfolds to body.subst 0 (mu A body).
      -- The needed conclusion requires coinductive reasoning about
      -- `Sub v_e v_τ` where v_τ = eval of the unfolded body.
      -- This is the canonical coinductive gap for self-type intro.
      sorry

/-- **Eval preservation**: If `[] ⊢ e ⊑ τ` and both `e` and `τ` evaluate to
    values `v_e` and `v_τ`, then `[] ⊢ v_e ⊑ v_τ`. -/
noncomputable def evalPreservation
    {e τ : Expr}
    (hsub : Sub [] e τ) (fuel fuel_τ : Nat)
    (v_e v_τ : Expr)
    (he : eval fuel e = some v_e) (hτ : eval fuel_τ τ = some v_τ)
    : Sub [] v_e v_τ :=
  evalPreservation_aux (fuel + fuel_τ) e τ hsub fuel fuel_τ v_e v_τ (Nat.le_refl _) he hτ

end Och.Simple
