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

/-- Subtyping relation. `Subtype' a b` means `a ⊑ b`.

    Trans is NOT a constructor (lambda inversion requires it). Instead,
    transitivity is proved as a theorem (`Subtype'.trans`) by structural
    induction on the second proof. -/
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
      A value that satisfies the body of a self-type is a member of that type. -/
  | self_intro {a : Expr} {x : Name} {ann body : Expr} :
      Subtype' a body → Subtype' a (.mu x ann body)

/-- Subtype' without self_intro. Used for absEval_mono where the IH never
    generates self_intro (monotonicity starts with .refl e and structural
    constructors preserve the no-self-intro invariant). This avoids 5
    unreachable sorry cases in the generalized monotonicity proof. -/
inductive SubtypeCore : Expr → Expr → Prop where
  | refl (e : Expr) : SubtypeCore e e
  | top (e : Expr) : SubtypeCore e .type
  | lam_body {x : Name} {dom body₁ body₂ : Expr} :
      SubtypeCore body₂ body₁ → SubtypeCore (.lam x dom body₂) (.lam x dom body₁)
  | app_cong {f₁ f₂ a₁ a₂ : Expr} :
      SubtypeCore f₂ f₁ → SubtypeCore a₂ a₁ → SubtypeCore (.app f₂ a₂) (.app f₁ a₁)
  | mu_body {x : Name} {ann body₁ body₂ : Expr} :
      SubtypeCore body₂ body₁ → SubtypeCore (.mu x ann body₂) (.mu x ann body₁)

/-- Every SubtypeCore is a Subtype'. -/
theorem SubtypeCore.toSubtype' {a b : Expr} (h : SubtypeCore a b) : Subtype' a b := by
  induction h with
  | refl e => exact .refl e
  | top e => exact .top e
  | lam_body _ ih => exact .lam_body ih
  | app_cong _ _ ihf iha => exact .app_cong ihf iha
  | mu_body _ ih => exact .mu_body ih

/-- If `SubtypeCore e (lam x d b)` then e is a lam with same name/domain. -/
theorem SubtypeCore.lam_rhs_shape {x : Name} {dom body : Expr} {e : Expr}
    (h : SubtypeCore e (.lam x dom body)) :
    ∃ body', e = .lam x dom body' ∧ SubtypeCore body' body := by
  cases h with
  | refl => exact ⟨body, rfl, .refl body⟩
  | lam_body h => exact ⟨_, rfl, h⟩

/-- If `SubtypeCore e (mu x a b)` then e is a mu with same binder/ann. -/
theorem SubtypeCore.mu_rhs_shape {x : Name} {ann body : Expr} {e : Expr}
    (h : SubtypeCore e (.mu x ann body)) :
    ∃ body', e = .mu x ann body' ∧ SubtypeCore body' body := by
  cases h with
  | refl => exact ⟨body, rfl, .refl body⟩
  | mu_body h => exact ⟨_, rfl, h⟩

/-- **SubtypeCore is transitive.** No self_intro means the proof is straightforward
    structural induction on the second argument. -/
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

/-- **Subtype' is transitive.** Proved by structural induction on the second
    proof. Each case either returns directly or recurses with a strictly
    smaller q. -/
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
    seen tracks assumed subtyping pairs for equi-recursive termination.

    Key rules:
    - Syntactic equality → true (reflexivity)
    - b = Type → true (Type is top)
    - Already in seen → true (equi-recursive coinductive hypothesis)
    - Both lambdas → contravariant domains, covariant bodies
    - Both mus → covariant bodies (same binder)
    - self-intro: a ⊑ mu x ann body  iff  a ⊑ body[x := a]  (with (a, mu) in seen)
    - self-elim: mu x ann body ⊑ b  iff  body[x := mu] ⊑ b  (with (mu, b) in seen)
    - Otherwise → infer type of a, check type ⊑ b (transitivity through type) -/
def subCheckNF (fuel : Nat) (ctx : List (Name × Expr))
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
      | .lam x domA bodyA, .lam y domB bodyB =>
        -- Function subtyping: contravariant domain, covariant body
        let bodyB' := if x == y then bodyB else bodyB.subst y (.var x)
        -- Normalize domB so inferType can pattern-match on it (e.g.,
        -- recognize Vec' T as a lambda rather than a beta-redex).
        let domB_norm := normalizeDomain fuel ctx domB
        subCheckNF fuel ctx seen domB domA
        && subCheckNF fuel ((x, domB_norm) :: ctx) seen bodyA bodyB'
      | .mu x _annA bodyA, .mu y _annB bodyB =>
        -- Mu subtyping: covariant in body (like iota_body)
        let bodyB' := if x == y then bodyB else bodyB.subst y (.var x)
        subCheckNF fuel ((x, .mu x _annA bodyA) :: ctx) seen bodyA bodyB'
      | _, .mu x _ann body =>
        -- Self-intro (equi-recursive): a ⊑ mu x ann body  iff  a ⊑ body[x := mu]
        -- Substitutes the mu TYPE (not the value a). This is the equi-recursive
        -- unfolding rule: mu x. body ≡ body[x := mu x. body]. Using the mu
        -- instead of `a` avoids nonsensical contravariant obligations when the
        -- self-variable is used in type positions (e.g., Variant B's MuNat where
        -- N appears as a domain type). For Cedille-style self types where the
        -- self-variable is unused (Variant A), both substitutions are equivalent.
        -- Dependent elimination is unaffected (goes through self-elim, not intro).
        -- Add (a, mu) to seen for equi-recursive coinduction.
        subCheckNF fuel ctx ((a, b) :: seen) a (body.subst x b)
      | .mu x ann body, _ =>
        -- Self-elim: mu x ann body ⊑ b  iff  body[x := mu x ann body] ⊑ b
        -- Add (mu, b) to seen for the same reason.
        subCheckNF fuel ctx ((a, b) :: seen) (body.subst x (.mu x ann body)) b
      | _, _ =>
        match inferType ctx a with
        | some ty => subCheckNF fuel ctx seen ty b
        | none => false

/-- Decidable subtyping check. Normalizes both sides via absEval, then
    compares structurally with pointwise function subtyping and type
    inference for neutral terms. -/
def subCheck (fuel : Nat) (a b : Expr) : Bool :=
  match absEval fuel [] a, absEval fuel [] b with
  | some a', some b' => subCheckNF fuel [] [] a' b'
  | _, _ => false
