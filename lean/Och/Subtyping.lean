import Och.Syntax
import Och.Eval

/-!
# Och Subtyping

Subtyping is set inclusion. `A ⊑ B` means every value in A is also in B.

For lambda terms this is checked pointwise:
  `λ(x: A₁). B₁ ⊑ λ(x: A₂). B₂` if `A₂ ⊑ A₁` (contravariant) and
  `B₁ ⊑ B₂` for all `x ⊑ A₂` (covariant, checked with x as neutral).

Type is top: `τ ⊑ Type` for any τ.

mu replaces both fix and iota. Subtyping rules:
- mu-mu: covariant in body (same binder name)
- self-intro: a ⊑ mu x ann body  iff  a ⊑ body[x := a]
- self-elim: mu x ann body ⊑ b  iff  body[x := mu x ann body] ⊑ b
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
  /-- Mu body covariance (same binder name and annotation).
      If body₂ ⊑ body₁ then mu x ann body₂ ⊑ mu x ann body₁.
      Replaces both fix_cong and iota_body. -/
  | mu_body {x : Name} {ann body₁ body₂ : Expr} :
      Subtype' body₂ body₁ → Subtype' (.mu x ann body₂) (.mu x ann body₁)
  /-- Self-introduction: if `a ⊑ body` then `a ⊑ mu x ann body`.
      A value that satisfies the body of a self-type is a member of that type.
      Placed in Subtype' (not just SubtypeTrans) so that structural congruence
      lemmas in SubtypeTrans can compose with it via .step. -/
  | self_intro {a : Expr} {x : Name} {ann body : Expr} :
      Subtype' a body → Subtype' a (.mu x ann body)

/-- Transitive closure of Subtype'. Used in soundness where transitivity
    is needed (the asc case chains IH result with the well-typedness hyp). -/
inductive SubtypeTrans : Expr → Expr → Prop where
  /-- Lift a single-step subtyping into the transitive closure. -/
  | step {a b : Expr} : Subtype' a b → SubtypeTrans a b
  /-- Transitivity. -/
  | trans {a b c : Expr} : SubtypeTrans a b → SubtypeTrans b c → SubtypeTrans a c
  /-- Self-introduction: if `a ⊑ body'` then `a ⊑ mu x ann body'`.
      Takes a Subtype' (not SubtypeTrans) so that congruence lemmas
      (lam_body, mu_body, app_cong) can handle this case without circularity.
      For SubtypeTrans chains, use `.trans h (.step (.self_intro (.refl body')))`. -/
  | self_intro {a : Expr} {x : Name} {ann body' : Expr} :
      Subtype' a body' → SubtypeTrans a (.mu x ann body')

/-- Lift lam_body through SubtypeTrans: if bodies are related transitively,
    then the lambdas are related transitively. -/
theorem SubtypeTrans.lam_body {x : Name} {dom body₁ body₂ : Expr}
    (h : SubtypeTrans body₂ body₁) :
    SubtypeTrans (.lam x dom body₂) (.lam x dom body₁) := by
  induction h with
  | step h => exact .step (.lam_body h)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | self_intro h' =>
    -- h' : Subtype' body₂ body_inner, body₁ = mu y ann body_inner
    -- Build: (lam body₂) ⊑ (lam body_inner) ⊑ (lam (mu body_inner))
    exact .trans (.step (.lam_body h')) (.step (.lam_body (.self_intro (.refl _))))

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

/-- If `Subtype' (lam x d b) e` then `e` is a lam, Type, or mu (via self-intro).
    Used to eliminate impossible mixed cases in monotonicity. -/
theorem Subtype'.lam_lhs_cases {x : Name} {dom body : Expr} {e : Expr}
    (h : Subtype' (.lam x dom body) e) :
    (∃ body', e = .lam x dom body' ∧ Subtype' body body') ∨ e = .type ∨
    (∃ y ann body', e = .mu y ann body' ∧ Subtype' (.lam x dom body) body') := by
  cases h with
  | refl => exact Or.inl ⟨body, rfl, Subtype'.refl body⟩
  | top _ => exact Or.inr (Or.inl rfl)
  | lam_body h => exact Or.inl ⟨_, rfl, h⟩
  | self_intro h => exact Or.inr (Or.inr ⟨_, _, _, rfl, h⟩)

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
  | self_intro _ => intro _ _ _ hb; exact absurd hb (by intro h; cases h)

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
  | self_intro _ => intro _ _ hb; exact absurd hb (by intro h; cases h)

/-- If `SubtypeTrans e (app f a)` then e is an app with related parts. -/
theorem SubtypeTrans.app_target_shape {f a : Expr} {e : Expr}
    (h : SubtypeTrans e (.app f a)) :
    ∃ f' a', e = .app f' a' ∧ SubtypeTrans f' f ∧ SubtypeTrans a' a :=
  h.app_target_shape_aux rfl

/-- Helper: if every Subtype' step into `b` is refl and b is not a mu target
    of self_intro, then SubtypeTrans e b → e = b. -/
private theorem SubtypeTrans.eq_of_rigid_target {e b : Expr}
    (h : SubtypeTrans e b)
    (rigid : ∀ a, Subtype' a b → a = b) :
    e = b := by
  induction h with
  | step h' => exact rigid _ h'
  | trans _ _ ih₁ ih₂ =>
    have hmid := ih₂ rigid
    subst hmid
    exact ih₁ rigid
  | self_intro h' =>
    -- h' : Subtype' e body_inner, b = mu y ann body_inner
    -- rigid gives: Subtype' e (mu y ann body_inner) → e = mu y ann body_inner
    exact rigid _ (.self_intro h')

/-- If `SubtypeTrans e (var x)` then `e = var x`. -/
theorem SubtypeTrans.var_target {x : Name} {e : Expr}
    (h : SubtypeTrans e (.var x)) : e = .var x :=
  h.eq_of_rigid_target (fun _ h => by cases h with | refl => rfl)

/-- If `SubtypeTrans e (asc t τ)` then `e = asc t τ`. -/
theorem SubtypeTrans.asc_target {t τ : Expr} {e : Expr}
    (h : SubtypeTrans e (.asc t τ)) : e = .asc t τ :=
  h.eq_of_rigid_target (fun _ h => by cases h with | refl => rfl)

/-- If `Subtype' e (mu x ann body)` then either e is a mu with related body,
    or e subtypes the body directly (self-intro). -/
theorem Subtype'.mu_rhs_shape {x : Name} {ann body : Expr} {e : Expr}
    (h : Subtype' e (.mu x ann body)) :
    (∃ body', e = .mu x ann body' ∧ Subtype' body' body) ∨ Subtype' e body := by
  cases h with
  | refl => exact Or.inl ⟨body, rfl, Subtype'.refl body⟩
  | mu_body h => exact Or.inl ⟨_, rfl, h⟩
  | self_intro h => exact Or.inr h

-- NOTE: mu_target_shape is no longer valid with self_intro. With self_intro,
-- SubtypeTrans a (mu x ann body) can hold for any a, not just another mu.

/-- Lift mu_body through SubtypeTrans. -/
theorem SubtypeTrans.mu_body {x : Name} {ann body₁ body₂ : Expr}
    (h : SubtypeTrans body₂ body₁) :
    SubtypeTrans (.mu x ann body₂) (.mu x ann body₁) := by
  induction h with
  | step h => exact .step (.mu_body h)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | self_intro h' =>
    exact .trans (.step (.mu_body h')) (.step (.mu_body (.self_intro (.refl _))))

/-- Mu inversion: if `Subtype' (mu x a b₂) (mu x a b₁)` then either bodies
    are related or (mu x a b₂) subtypes b₁ directly (self-intro). -/
theorem Subtype'.mu_inv {x : Name} {ann body₁ body₂ : Expr}
    (h : Subtype' (.mu x ann body₂) (.mu x ann body₁)) :
    Subtype' body₂ body₁ ∨ Subtype' (.mu x ann body₂) body₁ := by
  cases h with
  | refl => exact Or.inl (Subtype'.refl body₁)
  | mu_body h => exact Or.inl h
  | self_intro h => exact Or.inr h

-- NOTE: mu_inv for SubtypeTrans is no longer provable with self_intro.
-- self_intro allows SubtypeTrans (mu ...) (mu ...) without bodies being related.

/-- Congruence for app through SubtypeTrans (left component). -/
private theorem SubtypeTrans.app_cong_left {f₁ f₂ : Expr} (a : Expr)
    (hf : SubtypeTrans f₂ f₁) :
    SubtypeTrans (.app f₂ a) (.app f₁ a) := by
  induction hf with
  | step h => exact .step (.app_cong h (.refl a))
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | self_intro h' =>
    exact .trans (.step (.app_cong h' (.refl a))) (.step (.app_cong (.self_intro (.refl _)) (.refl a)))

/-- Congruence for app through SubtypeTrans (right component). -/
private theorem SubtypeTrans.app_cong_right (f : Expr) {a₁ a₂ : Expr}
    (ha : SubtypeTrans a₂ a₁) :
    SubtypeTrans (.app f a₂) (.app f a₁) := by
  induction ha with
  | step h => exact .step (.app_cong (.refl f) h)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | self_intro h' =>
    exact .trans (.step (.app_cong (.refl f) h')) (.step (.app_cong (.refl f) (.self_intro (.refl _))))

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
    | some (.mu x _ann body) =>
      -- Self-type elimination: f : mu x ann body → f : body[x := f]
      -- Unfold the self type, then try to infer application type
      let unfolded := body.subst x f
      match unfolded with
      | .lam y _dom retTy => some (retTy.subst y a)
      | _ => none
    | _ => none
  | _ => none

/-- Normalize a domain expression using ctx variables as neutrals.
    Domains in absEval output are deliberately left unnormalized (to preserve
    monotonicity), but subCheckNF's inferType needs normalized types to
    pattern-match on (e.g., recognizing `Vec' T` as a lambda). -/
private def normalizeDomain (fuel : Nat) (ctx : List (Name × Expr)) (dom : Expr) : Expr :=
  let env : Env := ctx.map fun (n, _) => (n, .var n)
  match absEval fuel env dom with
  | some d => d
  | none => dom

/-- Structural subtype check on normalized terms.
    ctx tracks (variable_name, declared_domain) for bound variables.

    Key rules:
    - Syntactic equality → true (reflexivity)
    - b = Type → true (Type is top)
    - Both lambdas → contravariant domains, covariant bodies
    - Both mus → covariant bodies (same binder)
    - self-intro: a ⊑ mu x ann body  iff  a ⊑ body[x := a]
    - self-elim: mu x ann body ⊑ b  iff  body[x := mu x ann body] ⊑ b
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
        -- Normalize domB so inferType can pattern-match on it (e.g.,
        -- recognize Vec' T as a lambda rather than a beta-redex).
        let domB_norm := normalizeDomain fuel ctx domB
        subCheckNF fuel ctx domB domA
        && subCheckNF fuel ((x, domB_norm) :: ctx) bodyA bodyB'
      | .mu x _annA bodyA, .mu y _annB bodyB =>
        -- Mu subtyping: covariant in body (like iota_body)
        let bodyB' := if x == y then bodyB else bodyB.subst y (.var x)
        subCheckNF fuel ((x, .mu x _annA bodyA) :: ctx) bodyA bodyB'
      | _, .mu x _ann body =>
        -- Self-intro: a ⊑ mu x ann body  iff  a ⊑ body[x := a]
        subCheckNF fuel ctx a (body.subst x a)
      | .mu x ann body, _ =>
        -- Self-elim: mu x ann body ⊑ b  iff  body[x := mu x ann body] ⊑ b
        subCheckNF fuel ctx (body.subst x (.mu x ann body)) b
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
