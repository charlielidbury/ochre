import Och.Syntax
import Och.Eval

/-!
# Och Subtyping

Subtyping is set inclusion. `A ⊑ B` means every value in A is also in B.

For lambda terms this is checked pointwise:
  `λ(x: A₁). B₁ ⊑ λ(x: A₂). B₂` if `A₂ ⊑ A₁` (contravariant) and
  `B₁ ⊑ B₂` for all `x ⊑ A₂` (covariant, checked with x as neutral).

Type is top: `τ ⊑ Type` for any τ.
-/

open Expr

/-- Subtyping relation (trans-free). `Subtype' a b` means `a ⊑ b`.

    Trans is deliberately excluded so that lambda inversion is possible:
    `Subtype' (lam x d b₂) (lam x d b₁)` can only arise from `refl` or
    `lam_body`, both of which give `b₂ ⊑ b₁`. This is essential for the
    monotonicity proof's app case. -/
inductive Subtype' : Expr → Expr → Prop where
  /-- Reflexivity: `e ⊑ e` -/
  | refl (e : Expr) : Subtype' e e
  /-- Type is top: `e ⊑ Type` for any `e` -/
  | top (e : Expr) : Subtype' e .type
  /-- Lambda body covariance (same name and domain).
      If body₂ ⊑ body₁ then λx:dom. body₂ ⊑ λx:dom. body₁.
      Used in the monotonicity proof for the lambda case. -/
  | lam_body {x : Name} {dom body₁ body₂ : Expr} :
      Subtype' body₂ body₁ → Subtype' (.lam x dom body₂) (.lam x dom body₁)
  /-- Neutral application congruence.
      If f₂ ⊑ f₁ and a₂ ⊑ a₁ then (f₂ a₂) ⊑ (f₁ a₁).
      Used in the monotonicity proof for stuck applications. -/
  | app_cong {f₁ f₂ a₁ a₂ : Expr} :
      Subtype' f₂ f₁ → Subtype' a₂ a₁ → Subtype' (.app f₂ a₂) (.app f₁ a₁)
  /-- Fix congruence: if e₂ ⊑ e₁ then fix e₂ ⊑ fix e₁. -/
  | fix_cong {e₁ e₂ : Expr} :
      Subtype' e₂ e₁ → Subtype' (.fix e₂) (.fix e₁)
  /-- Iota body covariance (same binder name).
      If body₂ ⊑ body₁ then iota x body₂ ⊑ iota x body₁.
      Mirrors lam_body for self types. -/
  | iota_body {x : Name} {body₁ body₂ : Expr} :
      Subtype' body₂ body₁ → Subtype' (.iota x body₂) (.iota x body₁)

/-- Transitive closure of Subtype'. Used in soundness where transitivity
    is needed (the asc case chains IH result with the well-typedness hyp). -/
inductive SubtypeTrans : Expr → Expr → Prop where
  /-- Lift a single-step subtyping into the transitive closure. -/
  | step {a b : Expr} : Subtype' a b → SubtypeTrans a b
  /-- Transitivity. -/
  | trans {a b c : Expr} : SubtypeTrans a b → SubtypeTrans b c → SubtypeTrans a c

/-- Lift lam_body through SubtypeTrans: if bodies are related transitively,
    then the lambdas are related transitively. -/
theorem SubtypeTrans.lam_body {x : Name} {dom body₁ body₂ : Expr}
    (h : SubtypeTrans body₂ body₁) :
    SubtypeTrans (.lam x dom body₂) (.lam x dom body₁) := by
  induction h with
  | step h => exact .step (.lam_body h)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Lambda inversion: if `Subtype' (lam x d b₂) (lam x d b₁)` then `Subtype' b₂ b₁`.
    This is the key lemma enabled by removing trans from Subtype'. -/
theorem Subtype'.lam_inv {x : Name} {dom body₁ body₂ : Expr}
    (h : Subtype' (.lam x dom body₂) (.lam x dom body₁)) : Subtype' body₂ body₁ := by
  cases h with
  | refl => exact Subtype'.refl body₁
  | lam_body h => exact h

/-- If `Subtype' e (lam x d b)` then `e` must be a lam with same name and domain.
    Essential for eliminating mixed lam/non-lam cases in proofs. -/
theorem Subtype'.lam_rhs_shape {x : Name} {dom body : Expr} {e : Expr}
    (h : Subtype' e (.lam x dom body)) :
    ∃ body', e = .lam x dom body' ∧ Subtype' body' body := by
  cases h with
  | refl => exact ⟨body, rfl, Subtype'.refl body⟩
  | lam_body h => exact ⟨_, rfl, h⟩

/-- If `Subtype' (lam x d b) e` then `e` is either a lam or Type.
    Used to eliminate impossible mixed cases in monotonicity. -/
theorem Subtype'.lam_lhs_cases {x : Name} {dom body : Expr} {e : Expr}
    (h : Subtype' (.lam x dom body) e) :
    (∃ body', e = .lam x dom body' ∧ Subtype' body body') ∨ e = .type := by
  cases h with
  | refl => exact Or.inl ⟨body, rfl, Subtype'.refl body⟩
  | top _ => exact Or.inr rfl
  | lam_body h => exact Or.inl ⟨_, rfl, h⟩

/-- Helper: generalized lam target shape with variable target. -/
private theorem SubtypeTrans.lam_target_shape_aux {e b : Expr}
    (h : SubtypeTrans e b) :
    ∀ {x : Name} {dom body : Expr}, b = .lam x dom body →
    ∃ body', e = .lam x dom body' ∧ SubtypeTrans body' body := by
  induction h with
  | step h' =>
    intro x dom body hb; subst hb
    obtain ⟨body', eq, hsub⟩ := Subtype'.lam_rhs_shape h'
    exact ⟨body', eq, .step hsub⟩
  | trans _ _ ih₁ ih₂ =>
    intro x dom body hb
    obtain ⟨b_mid, eq_mid, h_mid_b⟩ := ih₂ hb
    obtain ⟨b', eq', h_b'_mid⟩ := ih₁ eq_mid
    exact ⟨b', eq', .trans h_b'_mid h_mid_b⟩

/-- If `SubtypeTrans e (lam x d b)` then e is a lam with same name/domain. -/
theorem SubtypeTrans.lam_target_shape {x : Name} {dom body : Expr} {e : Expr}
    (h : SubtypeTrans e (.lam x dom body)) :
    ∃ body', e = .lam x dom body' ∧ SubtypeTrans body' body :=
  h.lam_target_shape_aux rfl

/-- Lambda inversion for SubtypeTrans. -/
theorem SubtypeTrans.lam_inv {x : Name} {dom body₁ body₂ : Expr}
    (h : SubtypeTrans (.lam x dom body₂) (.lam x dom body₁)) :
    SubtypeTrans body₂ body₁ := by
  obtain ⟨body', eq, hsub⟩ := h.lam_target_shape
  cases eq; exact hsub

/-- Helper: generalized app target shape with variable target. -/
private theorem SubtypeTrans.app_target_shape_aux {e b : Expr}
    (h : SubtypeTrans e b) :
    ∀ {f a : Expr}, b = .app f a →
    ∃ f' a', e = .app f' a' ∧ SubtypeTrans f' f ∧ SubtypeTrans a' a := by
  induction h with
  | step h' =>
    intro f a hb; subst hb
    cases h' with
    | refl => exact ⟨f, a, rfl, .step (.refl f), .step (.refl a)⟩
    | app_cong hf ha => exact ⟨_, _, rfl, .step hf, .step ha⟩
  | trans _ _ ih₁ ih₂ =>
    intro f a hb
    obtain ⟨f_mid, a_mid, eq_mid, hf_mid, ha_mid⟩ := ih₂ hb
    obtain ⟨f', a', eq', hf', ha'⟩ := ih₁ eq_mid
    exact ⟨f', a', eq', .trans hf' hf_mid, .trans ha' ha_mid⟩

/-- If `SubtypeTrans e (app f a)` then e is an app with related parts. -/
theorem SubtypeTrans.app_target_shape {f a : Expr} {e : Expr}
    (h : SubtypeTrans e (.app f a)) :
    ∃ f' a', e = .app f' a' ∧ SubtypeTrans f' f ∧ SubtypeTrans a' a :=
  h.app_target_shape_aux rfl

/-- If every Subtype' step into `b` is refl, then SubtypeTrans e b → e = b. -/
theorem SubtypeTrans.eq_of_rigid_target {e b : Expr}
    (h : SubtypeTrans e b)
    (rigid : ∀ a, Subtype' a b → a = b) :
    e = b := by
  induction h with
  | step h' => exact rigid _ h'
  | trans _ _ ih₁ ih₂ =>
    have hmid := ih₂ rigid
    subst hmid
    exact ih₁ rigid

/-- If `SubtypeTrans e (var x)` then `e = var x`. -/
theorem SubtypeTrans.var_target {x : Name} {e : Expr}
    (h : SubtypeTrans e (.var x)) : e = .var x :=
  h.eq_of_rigid_target (fun _ h => by cases h with | refl => rfl)

/-- If `SubtypeTrans e (asc t τ)` then `e = asc t τ`. -/
theorem SubtypeTrans.asc_target {t τ : Expr} {e : Expr}
    (h : SubtypeTrans e (.asc t τ)) : e = .asc t τ :=
  h.eq_of_rigid_target (fun _ h => by cases h with | refl => rfl)

/-- If `Subtype' e (fix inner)` then `e` is a fix with related inner. -/
theorem Subtype'.fix_rhs_shape {inner : Expr} {e : Expr}
    (h : Subtype' e (.fix inner)) :
    ∃ inner', e = .fix inner' ∧ Subtype' inner' inner := by
  cases h with
  | refl => exact ⟨inner, rfl, Subtype'.refl inner⟩
  | fix_cong h => exact ⟨_, rfl, h⟩

/-- Helper: generalized fix target shape with variable target. -/
private theorem SubtypeTrans.fix_target_shape_aux {e b : Expr}
    (h : SubtypeTrans e b) :
    ∀ {inner : Expr}, b = .fix inner →
    ∃ inner', e = .fix inner' ∧ SubtypeTrans inner' inner := by
  induction h with
  | step h' =>
    intro inner hb; subst hb
    obtain ⟨inner', eq, hsub⟩ := Subtype'.fix_rhs_shape h'
    exact ⟨inner', eq, .step hsub⟩
  | trans _ _ ih₁ ih₂ =>
    intro inner hb
    obtain ⟨inner_mid, eq_mid, h_mid⟩ := ih₂ hb
    obtain ⟨inner', eq', h'⟩ := ih₁ eq_mid
    exact ⟨inner', eq', .trans h' h_mid⟩

/-- If `SubtypeTrans e (fix inner)` then e is a fix with related inner. -/
theorem SubtypeTrans.fix_target_shape {inner : Expr} {e : Expr}
    (h : SubtypeTrans e (.fix inner)) :
    ∃ inner', e = .fix inner' ∧ SubtypeTrans inner' inner :=
  h.fix_target_shape_aux rfl

/-- Lift iota_body through SubtypeTrans. -/
theorem SubtypeTrans.iota_body {x : Name} {body₁ body₂ : Expr}
    (h : SubtypeTrans body₂ body₁) :
    SubtypeTrans (.iota x body₂) (.iota x body₁) := by
  induction h with
  | step h => exact .step (.iota_body h)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Iota inversion: if `Subtype' (iota x b₂) (iota x b₁)` then `Subtype' b₂ b₁`. -/
theorem Subtype'.iota_inv {x : Name} {body₁ body₂ : Expr}
    (h : Subtype' (.iota x body₂) (.iota x body₁)) : Subtype' body₂ body₁ := by
  cases h with
  | refl => exact Subtype'.refl body₁
  | iota_body h => exact h

/-- If `Subtype' e (iota x body)` then `e` must be an iota with same name. -/
theorem Subtype'.iota_rhs_shape {x : Name} {body : Expr} {e : Expr}
    (h : Subtype' e (.iota x body)) :
    ∃ body', e = .iota x body' ∧ Subtype' body' body := by
  cases h with
  | refl => exact ⟨body, rfl, Subtype'.refl body⟩
  | iota_body h => exact ⟨_, rfl, h⟩

/-- Helper: generalized iota target shape with variable target. -/
private theorem SubtypeTrans.iota_target_shape_aux {e b : Expr}
    (h : SubtypeTrans e b) :
    ∀ {x : Name} {body : Expr}, b = .iota x body →
    ∃ body', e = .iota x body' ∧ SubtypeTrans body' body := by
  induction h with
  | step h' =>
    intro x body hb; subst hb
    obtain ⟨body', eq, hsub⟩ := Subtype'.iota_rhs_shape h'
    exact ⟨body', eq, .step hsub⟩
  | trans _ _ ih₁ ih₂ =>
    intro x body hb
    obtain ⟨b_mid, eq_mid, h_mid_b⟩ := ih₂ hb
    obtain ⟨b', eq', h_b'_mid⟩ := ih₁ eq_mid
    exact ⟨b', eq', .trans h_b'_mid h_mid_b⟩

/-- If `SubtypeTrans e (iota x body)` then e is an iota with same name. -/
theorem SubtypeTrans.iota_target_shape {x : Name} {body : Expr} {e : Expr}
    (h : SubtypeTrans e (.iota x body)) :
    ∃ body', e = .iota x body' ∧ SubtypeTrans body' body :=
  h.iota_target_shape_aux rfl

/-- Iota inversion for SubtypeTrans. -/
theorem SubtypeTrans.iota_inv {x : Name} {body₁ body₂ : Expr}
    (h : SubtypeTrans (.iota x body₂) (.iota x body₁)) :
    SubtypeTrans body₂ body₁ := by
  obtain ⟨body', eq, hsub⟩ := h.iota_target_shape
  cases eq; exact hsub

/-- Congruence for app through SubtypeTrans (left component). -/
private theorem SubtypeTrans.app_cong_left {f₁ f₂ : Expr} (a : Expr)
    (hf : SubtypeTrans f₂ f₁) :
    SubtypeTrans (.app f₂ a) (.app f₁ a) := by
  induction hf with
  | step h => exact .step (.app_cong h (.refl a))
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Congruence for app through SubtypeTrans (right component). -/
private theorem SubtypeTrans.app_cong_right (f : Expr) {a₁ a₂ : Expr}
    (ha : SubtypeTrans a₂ a₁) :
    SubtypeTrans (.app f a₂) (.app f a₁) := by
  induction ha with
  | step h => exact .step (.app_cong (.refl f) h)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Congruence for app through SubtypeTrans. -/
theorem SubtypeTrans.app_cong {f₁ f₂ a₁ a₂ : Expr}
    (hf : SubtypeTrans f₂ f₁) (ha : SubtypeTrans a₂ a₁) :
    SubtypeTrans (.app f₂ a₂) (.app f₁ a₁) :=
  .trans (app_cong_left a₂ hf) (app_cong_right f₁ ha)

/-- Infer the type of a neutral term from a typing context.
    Variables have their declared type; applications use the function's
    return type (substituting the argument). -/
private def inferType (ctx : List (Name × Expr)) : Expr → Option Expr
  | .var x =>
    match ctx with
    | [] => none
    | (y, ty) :: rest => if y == x then some ty else inferType rest (.var x)
  | .app f a =>
    match inferType ctx f with
    | some (.lam x _dom retTy) => some (retTy.subst x a)
    | some (.iota _x _body) =>
      -- TODO: Self-type elimination: unfold iota and infer
      none
    | _ => none
  | _ => none

/-- Structural subtype check on normalized terms.
    ctx tracks (variable_name, declared_domain) for bound variables.

    Key rules:
    - Syntactic equality → true (reflexivity)
    - b = Type → true (Type is top)
    - Both lambdas → contravariant domains, covariant bodies
    - Otherwise → infer type of a, check type ⊑ b (transitivity through type) -/
private def subCheckNF (fuel : Nat) (ctx : List (Name × Expr)) (a b : Expr) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    if a == b then true
    else match b with
    | .type => true
    | _ =>
      match a, b with
      | .lam x domA bodyA, .lam y domB bodyB =>
        -- Function subtyping: contravariant domain, covariant body
        let bodyB' := if x == y then bodyB else bodyB.subst y (.var x)
        subCheckNF fuel ctx domB domA
        && subCheckNF fuel ((x, domB) :: ctx) bodyA bodyB'
      | .iota x bodyA, .iota y bodyB =>
        -- Self-type subtyping: covariant in body (like lam_body)
        let bodyB' := if x == y then bodyB else bodyB.subst y (.var x)
        subCheckNF fuel ((x, .iota x bodyA) :: ctx) bodyA bodyB'
      | _, _ =>
        match inferType ctx a with
        | some ty => subCheckNF fuel ctx ty b
        | none => false

/-- Decidable subtyping check. Normalizes both sides via absEval, then
    compares structurally with pointwise function subtyping and type
    inference for neutral terms. -/
def subCheck (fuel : Nat) (a b : Expr) : Bool :=
  match absEval fuel [] a, absEval fuel [] b with
  | some a', some b' => subCheckNF fuel [] a' b'
  | _, _ => false
