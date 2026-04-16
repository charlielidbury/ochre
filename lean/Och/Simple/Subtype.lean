import Och.Simple.Syntax

/-!
# Subtype relation for Simple Och (with split ι / fix)

Formalizes the relation `Γ ⊢ a ⊑ b` from the simplified Och calculus
spec, extended with two separate binders:

- `ι A. b`  — iota (self-type binder). Intro rule `iotaIntro` admits a
  value `a` at the self-type if `a ⊑ A` and `a ⊑ b[self := ι A. b]`.
  The "fixed-self" substitution (not the value) is used because that
  formulation admits an inductive transitivity proof (see research
  note in `docs/research/iota-fix-split.md`).

- `fix A. b`  — fix (recursive binder). Two rules:
  * `fixAnn` on RHS: `a ⊑ fix A. b` if `a ⊑ A` (annotation widening).
  * `unfoldFix` on LHS: unfolding a fix-value replaces the bound
    reference with the fix itself. Equi-recursive flavour.

## Rule selection rationale

The whiteboard theorem is:
```
cBool = λA:⊤. A → A → A
Bool  = ι self:cBool. λP:(cBool → ⊤). P true → P false → P self
true  = λA:⊤. λt:A. λf:A. t
```
and we want `∅ ⊢ true ⊑ Bool`.

Only `ι` is used — no `fix`. So for the target theorem we only need:
- [Iota-Intro] on the RHS.
- Nothing for fix (but we still add fix rules for completeness of the
  split — if soundness breaks for fix, the theorem is still closable).

The reason we keep the fixed-self form (not the precise / value-subst
form) is:

    Fixed form:    a ⊑ ι. b  ←  a ⊑ A  ∧  a ⊑ b[self := ι. b]
    Precise form:  a ⊑ ι. b  ←  a ⊑ A  ∧  a ⊑ b[self := a]

The precise form has cleaner semantic behaviour — both sides get the
same value in self-positions, so reflexivity often closes. But its
transitivity proof is blocked: substituting unrelated values in the
self-position of the cut formula creates a new, unrelated obligation.
The fixed form keeps the cut formula `ι. b` invariant across trans
cases (see Properties.lean `iotaIntro × iotaIntro` case) and admits a
clean proof.

Trade-off: the fixed form requires that `b[self := ι. b]` be closed
under the same reasoning as `b[self := a]` — i.e. it handles covariant
self-references cleanly, but contravariant self-references still cycle.
The whiteboard `Bool` has only covariant self-references, so it works.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

/-- A context is a list of types, with index 0 being the most recent binding. -/
abbrev Ctx := List Expr

namespace Ctx

/-- Look up the type at de Bruijn index `n` in the context.
    Returns the type shifted up by `n + 1` so that its free variables
    refer to the correct binders at the usage site. -/
def get? (Γ : Ctx) (n : Nat) : Option Expr :=
  match List.get? Γ n with
  | some T => some (T.shift 0 (n + 1))
  | none   => none

end Ctx

/-- The subtype relation: `Sub Γ a b` means `Γ ⊢ a ⊑ b`. -/
inductive Sub : Ctx → Expr → Expr → Type where
  /-- [Refl]: `Γ ⊢ a ⊑ a` -/
  | refl (Γ : Ctx) (a : Expr) :
      Sub Γ a a
  /-- [Top]: `Γ ⊢ a ⊑ ⊤` -/
  | top (Γ : Ctx) (a : Expr) :
      Sub Γ a .top
  /-- [Var]: `Γ ⊢ x ⊑ b` if `Γ(x) = T` and `Γ ⊢ T ⊑ b`. -/
  | var (Γ : Ctx) (x : Nat) (b T : Expr) :
      Γ.get? x = some T →
      Sub Γ T b →
      Sub Γ (.var x) b
  /-- [Lam]: `Γ ⊢ λA. b₁ ⊑ λB. b₂` if `Γ ⊢ B ⊑ A` and `B :: Γ ⊢ b₁ ⊑ b₂`. -/
  | lam (Γ : Ctx) (A B b₁ b₂ : Expr) :
      Sub Γ B A →
      Sub (B :: Γ) b₁ b₂ →
      Sub Γ (.lam A b₁) (.lam B b₂)
  /-- [App]: `Γ ⊢ f a ⊑ b` if `f` is callable with domain `D` and return `R`,
      `a ⊑ D`, and `R[0 := a] ⊑ b`. -/
  | app (Γ : Ctx) (f a b D R : Expr) :
      Sub Γ f (.lam D R) →
      Sub Γ a D →
      Sub Γ (R.subst 0 a) b →
      Sub Γ (.app f a) b
  /-- [Asc-L]: `Γ ⊢ (e : τ) ⊑ b` if `e ⊑ τ` and `τ ⊑ b`. -/
  | ascL (Γ : Ctx) (e τ b : Expr) :
      Sub Γ e τ →
      Sub Γ τ b →
      Sub Γ (.asc e τ) b
  /-- [Asc-R]: `Γ ⊢ a ⊑ (e : τ)` if `e ⊑ τ` and `a ⊑ e`. -/
  | ascR (Γ : Ctx) (a e τ : Expr) :
      Sub Γ e τ →
      Sub Γ a e →
      Sub Γ a (.asc e τ)
  /-- [Iota-Intro]: `Γ ⊢ a ⊑ ι A. b` if `a ⊑ A` and `a ⊑ b[0 := ι A. b]`.
      Uses the "fixed self-reference" formulation where the self-binder is
      instantiated with the iota itself (NOT the value `a`). This is the
      formulation that admits a clean inductive transitivity proof (the
      cut formula `ι A. b` is preserved across iotaIntro × iotaIntro
      trans cases).

      Limitations: covariant self-references close via substitution →
      reflexivity chains; contravariant self-references still produce
      productive cycles that need cycle detection. -/
  | iotaIntro (Γ : Ctx) (a A b : Expr) :
      Sub Γ a A →
      Sub Γ a (b.subst 0 (.iota A b)) →
      Sub Γ a (.iota A b)
  /-- [Fix-Ann]: `Γ ⊢ a ⊑ fix A. b` if `a ⊑ A`. A weak, annotation-only
      rule: a value is at a fix-type if it has the annotation type.
      No recursive unfolding on the RHS — soundness is trivial.
      Use [Unfold-Fix-L] to unfold a fix-typed value on the LHS. -/
  | fixAnn (Γ : Ctx) (a A b : Expr) :
      Sub Γ a A →
      Sub Γ a (.fix A b)
  /-- [Unfold-Fix-L]: `Γ ⊢ fix A. b ⊑ c` if `b[0 := fix A. b] ⊑ c`.
      Equi-recursive unfolding on the LHS. Cut formula is `b[...]` which
      may be larger than `fix A. b`, so this rule is NOT cut-measure-safe
      in general. In practice this means transitivity through this rule
      needs restricted usage (e.g. only where the unfolded body is
      structurally smaller). For the whiteboard theorem this rule is
      not used. -/
  | unfoldFixL (Γ : Ctx) (A b c : Expr) :
      Sub Γ (b.subst 0 (.fix A b)) c →
      Sub Γ (.fix A b) c

end Och.Simple
