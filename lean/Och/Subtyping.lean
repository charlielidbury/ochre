import Och.Syntax
import Och.Eval

/-!
# Och Subtyping (de Bruijn)

Subtyping is set inclusion. `A ⊑ B` means every value in A is also in B.

With de Bruijn indices, lambda/mu subtyping no longer needs variable renaming:
alpha-equivalent terms are syntactically identical, so body comparison is direct.
-/

open Expr

/-- Subtyping relation. `Subtype' a b` means `a ⊑ b`. -/
inductive Subtype' : Expr → Expr → Prop where
  | refl (e : Expr) : Subtype' e e
  | top (e : Expr) : Subtype' e .type
  | lam_body {dom body₁ body₂ : Expr} :
      Subtype' body₂ body₁ → Subtype' (.lam dom body₂) (.lam dom body₁)
  | app_cong {f₁ f₂ a₁ a₂ : Expr} :
      Subtype' f₂ f₁ → Subtype' a₂ a₁ → Subtype' (.app f₂ a₂) (.app f₁ a₁)
  | mu_body {ann body₁ body₂ : Expr} :
      Subtype' body₂ body₁ → Subtype' (.mu ann body₂) (.mu ann body₁)
  | self_intro {a : Expr} {ann body : Expr} :
      Subtype' a body → Subtype' a (.mu ann body)

/-- SubtypeCore: Subtype' without self_intro. Used for monotonicity/soundness. -/
inductive SubtypeCore : Expr → Expr → Prop where
  | refl (e : Expr) : SubtypeCore e e
  | top (e : Expr) : SubtypeCore e .type
  | lam_body {dom body₁ body₂ : Expr} :
      SubtypeCore body₂ body₁ → SubtypeCore (.lam dom body₂) (.lam dom body₁)
  | app_cong {f₁ f₂ a₁ a₂ : Expr} :
      SubtypeCore f₂ f₁ → SubtypeCore a₂ a₁ → SubtypeCore (.app f₂ a₂) (.app f₁ a₁)
  | mu_body {ann body₁ body₂ : Expr} :
      SubtypeCore body₂ body₁ → SubtypeCore (.mu ann body₂) (.mu ann body₁)

/-- SubtypeCore is preserved under shifting: if a ⊑ b then shift d c a ⊑ shift d c b. -/
theorem SubtypeCore.shift_preserve {a b : Expr} (h : SubtypeCore a b) (d c : Nat) :
    SubtypeCore (a.shift d c) (b.shift d c) := by
  induction h generalizing c with
  | refl e => exact .refl (e.shift d c)
  | top e => simp [Expr.shift]; exact .top (e.shift d c)
  | lam_body _ ih => simp [Expr.shift]; exact .lam_body (ih (c + 1))
  | app_cong _ _ ihf iha => simp [Expr.shift]; exact .app_cong (ihf c) (iha c)
  | mu_body _ ih => simp [Expr.shift]; exact .mu_body (ih (c + 1))

theorem SubtypeCore.toSubtype' {a b : Expr} (h : SubtypeCore a b) : Subtype' a b := by
  induction h with
  | refl e => exact .refl e
  | top e => exact .top e
  | lam_body _ ih => exact .lam_body ih
  | app_cong _ _ ihf iha => exact .app_cong ihf iha
  | mu_body _ ih => exact .mu_body ih

theorem SubtypeCore.lam_rhs_shape {dom body : Expr} {e : Expr}
    (h : SubtypeCore e (.lam dom body)) :
    ∃ body', e = .lam dom body' ∧ SubtypeCore body' body := by
  cases h with
  | refl => exact ⟨body, rfl, .refl body⟩
  | lam_body h => exact ⟨_, rfl, h⟩

theorem SubtypeCore.mu_rhs_shape {ann body : Expr} {e : Expr}
    (h : SubtypeCore e (.mu ann body)) :
    ∃ body', e = .mu ann body' ∧ SubtypeCore body' body := by
  cases h with
  | refl => exact ⟨body, rfl, .refl body⟩
  | mu_body h => exact ⟨_, rfl, h⟩

theorem SubtypeCore.trans : {a b c : Expr} → SubtypeCore a b → SubtypeCore b c → SubtypeCore a c := by
  intro a b c p q
  induction q generalizing a with
  | refl => exact p
  | top => exact .top a
  | lam_body h2 ih =>
    cases p with
    | refl => exact .lam_body h2
    | lam_body h1 => exact .lam_body (ih h1)
  | app_cong h2f h2a ihf iha =>
    cases p with
    | refl => exact .app_cong h2f h2a
    | app_cong h1f h1a => exact .app_cong (ihf h1f) (iha h1a)
  | mu_body h2 ih =>
    cases p with
    | refl => exact .mu_body h2
    | mu_body h1 => exact .mu_body (ih h1)

theorem Subtype'.trans : {a b c : Expr} → Subtype' a b → Subtype' b c → Subtype' a c := by
  intro a b c p q
  induction q generalizing a with
  | refl => exact p
  | top => exact .top a
  | lam_body h2 ih =>
    cases p with
    | refl => exact .lam_body h2
    | lam_body h1 => exact .lam_body (ih h1)
  | app_cong h2f h2a ihf iha =>
    cases p with
    | refl => exact .app_cong h2f h2a
    | app_cong h1f h1a => exact .app_cong (ihf h1f) (iha h1a)
  | mu_body h2 ih =>
    cases p with
    | refl => exact .mu_body h2
    | mu_body h1 => exact .mu_body (ih h1)
    | self_intro h1 => exact .self_intro (ih h1)
  | self_intro h2 ih => exact .self_intro (ih p)

/-- Infer the type of a neutral term from a typing context.
    ctx is a positional list: ctx[k] is the type/domain of bvar k. -/
def inferType (ctx : List Expr) : Expr → Option Expr
  | .bvar k => ctx.get? k
  | .app f a =>
    match inferType ctx f with
    | some (.lam _dom retTy) => some (retTy.subst 0 a)
    | some (.mu _ann body) =>
      -- Self-type elimination: unfold, then infer
      let unfolded := body.subst 0 f
      match unfolded with
      | .lam _dom retTy => some (retTy.subst 0 a)
      | _ => none
    | _ => none
  | _ => none

/-- Normalize a domain expression. Domains in absEval output are deliberately
    left unnormalized. subCheckNF's inferType needs them normalized to
    pattern-match (e.g., recognizing Vec' T as a lambda). -/
def normalizeDomain (fuel : Nat) (ctxLen : Nat) (dom : Expr) : Expr :=
  -- Build an identity env: bvar k → bvar k (all neutrals)
  let env : Env := (List.range ctxLen).map fun k => .bvar k
  match absEval fuel env dom with
  | some d => d
  | none => dom

/-- Structural subtype check on normalized terms.
    ctx: positional list of domain types for bound variables.
    seen: assumed subtyping pairs for equi-recursive termination. -/
def subCheckNF (fuel : Nat) (ctx : List Expr)
    (seen : List (Expr × Expr)) (a b : Expr) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if a == b then true
    else if seen.any (fun (a', b') => a == a' && b == b') then true
    else match b with
    | .type => true
    | _ =>
      match a, b with
      | .lam domA bodyA, .lam domB bodyB =>
        -- Function subtyping: contravariant domain, covariant body
        -- No renaming needed with de Bruijn — bodies already share bvar 0
        -- Normalize both domains: with de Bruijn + substitution, domains can
        -- contain unreduced applications that are semantically equal but
        -- syntactically different (e.g., Array 0 Nat vs Unit').
        let domA_norm := normalizeDomain fuel ctx.length domA
        let domB_norm := normalizeDomain fuel ctx.length domB
        subCheckNF fuel ctx seen domB_norm domA_norm
        -- Shift domB_norm: it was computed at the outer depth, but the bodies
        -- are one binder deeper.
        && subCheckNF fuel (Env.extend ctx (domB_norm.shift 1 0)) seen bodyA bodyB
      | .mu _annA bodyA, .mu _annB bodyB =>
        -- Mu subtyping: covariant in body. The mu value is at the outer depth,
        -- so shift it for the inner scope.
        subCheckNF fuel (Env.extend ctx (Expr.shift 1 0 (.mu _annA bodyA))) seen bodyA bodyB
      | _, .mu _ann body =>
        -- Self-intro (equi-recursive): a ⊑ mu ann body  iff  a ⊑ body[0 := mu]
        subCheckNF fuel ctx ((a, b) :: seen) a (body.subst 0 b)
      | .mu ann body, _ =>
        -- Self-elim: mu ann body ⊑ b  iff  body[0 := mu] ⊑ b
        subCheckNF fuel ctx ((a, b) :: seen) (body.subst 0 (.mu ann body)) b
      | _, _ =>
        match inferType ctx a with
        | some ty => subCheckNF fuel ctx seen ty b
        | none => false

/-- BEq on Expr is reflexive. Now trivial since BEq comes from DecidableEq. -/
theorem Expr.beq_refl (e : Expr) : (e == e) = true := by
  exact beq_self_eq_true e

/-- subCheckNF is reflexive: any expression is a subtype of itself.
    Follows from the BEq check `if a == b then true`. -/
theorem subCheckNF_refl (e : Expr) : subCheckNF 1 [] [] e e = true := by
  simp [subCheckNF, Expr.beq_refl]

/-- When subCheckNF succeeds for lam ⊑ lam (not by reflexivity),
    the body check also succeeds. Needed for VCompat.adequacy. -/
theorem subCheckNF_lam_lam_body {fuel : Nat} {ctx : List Expr} {dS bS dT bT : Expr}
    (h : subCheckNF (fuel + 1) ctx [] (Expr.lam dS bS) (Expr.lam dT bT) = true)
    (h_neq : Expr.lam dS bS ≠ Expr.lam dT bT) :
    ∃ fuel' ctx', subCheckNF fuel' ctx' [] bS bT = true := by
  unfold subCheckNF at h
  have h_beq : (Expr.lam dS bS == Expr.lam dT bT) = false :=
    beq_eq_false_iff_ne.mpr h_neq
  simp only [h_beq, ite_false, List.any_nil, Bool.false_eq_true, ite_true,
             Bool.and_eq_true] at h
  exact ⟨fuel, _, h.2⟩

/-- inferType returns none for lambda expressions. -/
theorem inferType_lam (ctx : List Expr) (dom body : Expr) :
    inferType ctx (Expr.lam dom body) = none := by
  rfl

/-- subCheckNF of (lam ...) against a non-equal, non-type, non-lam, non-mu
    target with empty seen returns false. -/
theorem subCheckNF_lam_impossible {fuel : Nat} {ctx : List Expr}
    {dom body b : Expr}
    (h : subCheckNF fuel ctx [] (Expr.lam dom body) b = true)
    (h_neq : Expr.lam dom body ≠ b)
    (h_not_type : b ≠ Expr.type)
    (h_not_lam : ∀ d b', b ≠ Expr.lam d b')
    (h_not_mu : ∀ a b', b ≠ Expr.mu a b') : False := by
  cases fuel with
  | zero => simp [subCheckNF] at h
  | succ k =>
    simp only [subCheckNF, beq_eq_false_iff_ne.mpr h_neq, ite_false, List.any_nil] at h
    cases b with
    | type => exact h_not_type rfl
    | lam d b' => exact h_not_lam d b' rfl
    | mu a b' => exact h_not_mu a b' rfl
    | bvar j => simp [inferType] at h
    | app f a => simp [inferType] at h
    | asc t ty => simp [inferType] at h

/-- When subCheckNF succeeds for mu ⊑ mu (not by reflexivity),
    the body check also succeeds. -/
theorem subCheckNF_mu_mu_body {fuel : Nat} {ctx : List Expr} {annS bodyS annT bodyT : Expr}
    (h : subCheckNF (fuel + 1) ctx [] (Expr.mu annS bodyS) (Expr.mu annT bodyT) = true)
    (h_neq : Expr.mu annS bodyS ≠ Expr.mu annT bodyT) :
    ∃ fuel' ctx', subCheckNF fuel' ctx' [] bodyS bodyT = true := by
  unfold subCheckNF at h
  simp only [beq_eq_false_iff_ne.mpr h_neq, ite_false, List.any_nil, Bool.and_eq_true] at h
  exact ⟨fuel, _, h⟩

/-- Decidable subtyping check. Normalizes both sides via absEval, then
    compares structurally. -/
def subCheck (fuel : Nat) (a b : Expr) : Bool :=
  match absEval fuel [] a, absEval fuel [] b with
  | some a', some b' => subCheckNF fuel [] [] a' b'
  | _, _ => false
