import Och.Simple.Syntax
import Och.Simple.Subtype

/-!
# Step-Indexed Subtyping for Simple Och

This file defines a step-indexed subtyping relation `SubN` that interprets
the subtyping judgment "semantically" via recursion on a natural-number
step-index. It exists to complement the inductive `Sub` relation with a
semantics for which transitivity is provable even in the presence of the
expressive `muR` rule (`self = subject`).

## The polarity problem

The expressive `muR` rule reads:
```
  Γ ⊢ a ⊑ A          Γ ⊢ a ⊑ b[0 := a]
  ------------------------------------
              Γ ⊢ a ⊑ μA. b
```
where `a` (not `μA.b`) is substituted into the body for the self-reference.

This form is strictly more expressive than the weaker variant (`self = μA.b`)
because it permits derivations like `dtrue ⊑ dBool` where `dBool`'s body,
after self-substitution, becomes a type that `dtrue` satisfies by
construction — but `dBool`'s body, after μA.b self-substitution, mentions
the motive `P` applied to `dtrue`, which `dtrue` (a closure over a *different*
index of `P`) doesn't satisfy.

The cost is transitivity. Given `a ⊑ b` and `b ⊑ μA.c`, the usual structural
induction asks us to produce `a ⊑ μA.c`, requiring `a ⊑ c[0 := a]`. The
premise we have from the RHS is `b ⊑ c[0 := b]`. Going from "b satisfies
c-with-self-b" to "a satisfies c-with-self-a" requires a substitution step
that is NOT monotonic in general (c may use its self-reference
contravariantly, e.g., as a function domain).

The literature (Gapeyev-Levin-Pierce, Danielsson-Altenkirch,
Ahmed/Appel-McAllester) resolves this by giving recursive types a
*semantic* (coinductive or step-indexed) interpretation. At step k+1, the
property "a ⊑ μA.c" means "at step k, a satisfies c-with-self-a". Every use
of the rule strictly decreases the step index, which gives us a well-founded
induction to reason about it.

## This file

This is a scaffolding/plan: we define `SubN` and prove the easy structural
facts (reflexivity, top). Transitivity is stated and partially proved,
with `sorry`s for the cases that cannot be discharged without the deeper
step-indexed arguments. See each `sorry` for a specific plan.

Completing the transitivity proof — together with `Sub Γ a b → ∀ k, SubN k Γ a b`
— provides the bridge by which the sorries in `Properties.lean`'s `Sub.trans`
can be eliminated: each `trans(X, muR)` case becomes "convert X and muR to
SubN k for all k, compose via SubN transitivity, and convert back."

## Why not define SubN via primitive recursion?

Lean 4 does not permit a direct `def SubN : Nat → ... → Prop` that case-splits
on the RHS and recurses at `k-1`, because the syntactic shape check on recursive
calls is fragile. We use a helper `SubBody` that takes the "recursion at lower
index" as an explicit parameter.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

/-- Single-step body of the step-indexed subtype relation.
    `R` is the "recursion at lower step index" — a parameter standing in for
    `SubN k` where the current index is `k+1`. All recursive calls go through `R`,
    strictly decreasing the step index. -/
def SubBody (R : Ctx → Expr → Expr → Prop) (Γ : Ctx) (a b : Expr) : Prop :=
  -- Base cases
  a = b
  ∨ b = .top
  ∨ (∃ x T, a = .var x ∧ Γ.get? x = some T ∧ R Γ T b)
  ∨ (∃ A₁ b₁ A₂ b₂, a = .lam A₁ b₁ ∧ b = .lam A₂ b₂ ∧ R Γ A₂ A₁ ∧ R (A₂ :: Γ) b₁ b₂)
  ∨ (∃ f a' D R_lam, a = .app f a' ∧ R Γ f (.lam D R_lam) ∧ R Γ a' D ∧ R Γ (R_lam.subst 0 a') b)
  ∨ (∃ e τ, a = .asc e τ ∧ R Γ e τ ∧ R Γ τ b)
  ∨ (∃ e τ, b = .asc e τ ∧ R Γ e τ ∧ R Γ a e)
  -- Mu on LHS: annotation route OR unfold route
  ∨ (∃ A body, a = .mu A body ∧ R Γ A b ∧ R (A :: Γ) body (A.shift 0 1))
  ∨ (∃ A body, a = .mu A body ∧ R (A :: Γ) body (A.shift 0 1) ∧ R Γ (body.subst 0 (.mu A body)) b)
  -- Mu on RHS: expressive muR (self = subject)
  ∨ (∃ A body, b = .mu A body ∧ R Γ a A ∧ R Γ a (body.subst 0 a))

/-- The step-indexed subtype relation. At index 0 everything holds (vacuous
    base case). At index k+1, the body is evaluated using `SubN k` for
    recursive calls. -/
def SubN : Nat → Ctx → Expr → Expr → Prop
  | 0, _, _, _ => True
  | k + 1, Γ, a, b => SubBody (SubN k) Γ a b

/-- Downward closure: SubN at k+1 implies SubN at k.
    This is the standard step-indexed "monotonicity in steps" lemma. -/
theorem SubN.downward : (k : Nat) → (Γ : Ctx) → (a b : Expr) →
    SubN (k + 1) Γ a b → SubN k Γ a b := by
  -- Plan: by strong induction on k. At k = 0, SubN 0 is True so vacuous.
  -- At k+1, unfold SubBody and show each case is preserved by IH.
  -- Each disjunct uses the SubN k premises; applying the IH at k-1 (which
  -- is the "deeper" recursive level) downgrades them to SubN (k-1).
  sorry

/-- Reflexivity of SubN at every step index.
    Plan: by induction on k. At k = 0, vacuous. At k+1, use the first
    disjunct of SubBody (a = b). -/
theorem SubN.refl : (k : Nat) → (Γ : Ctx) → (a : Expr) → SubN k Γ a a := by
  intro k Γ a
  cases k with
  | zero => trivial
  | succ k =>
    -- SubN (k+1) Γ a a = SubBody (SubN k) Γ a a. Choose the first disjunct.
    show SubBody (SubN k) Γ a a
    left
    rfl

/-- Top: everything is a subtype of top at every step index. -/
theorem SubN.top : (k : Nat) → (Γ : Ctx) → (a : Expr) → SubN k Γ a .top := by
  intro k Γ a
  cases k with
  | zero => trivial
  | succ k =>
    show SubBody (SubN k) Γ a .top
    right; left; rfl

/-- Transitivity of SubN. This is the main lemma motivating step-indexing.

    **Plan (by induction on k):**

    * `k = 0`: vacuous (both premises are `True`).

    * `k + 1`: case-split on the SubBody disjuncts that `hab` and `hbc` choose.
      For each combination, construct the appropriate SubBody witness for
      `SubN (k+1) Γ a c`. The recursive calls go through `SubN k` (using the
      IH) for all composition.

      The muR-on-RHS case is:
        `hab : SubN (k+1) Γ a b'`
        `hbc : SubN (k+1) Γ b' (μA.body)`, decomposing to
              `SubN k Γ b' A ∧ SubN k Γ b' (body.subst 0 b')`.
      Goal: `SubN (k+1) Γ a (μA.body)`, i.e., `SubN k Γ a A ∧ SubN k Γ a (body.subst 0 a)`.

      For `SubN k Γ a A`: apply `downward` to `hab`, compose with `SubN k Γ b' A`
      via IH transitivity.

      For `SubN k Γ a (body.subst 0 a)`: this is where the real work happens.
      We need to show that `a` satisfies the body with self=a. The key insight
      (Ahmed/Appel-McAllester) is that step-indexed equivalence of `a` and `b'`
      at step `k` means they are interchangeable in all contexts at step `k`.
      Formally, we need a substitution-compatibility lemma at `SubN k`:
        `SubN k Γ a b' → SubN k Γ b' (e.subst 0 b') → SubN k Γ a (e.subst 0 a)`
      for any open expression `e` (under `A :: Γ`).

    This substitution-compatibility lemma is itself proved by induction on
    `k`, mutually with transitivity. It is the core of the step-indexed
    argument. We leave it as a `sorry` with this plan for now.
-/
theorem SubN.trans : (k : Nat) → (Γ : Ctx) → (a b c : Expr) →
    SubN k Γ a b → SubN k Γ b c → SubN k Γ a c := by
  intro k Γ a b c hab hbc
  cases k with
  | zero => trivial
  | succ k =>
    -- Full case analysis on SubBody disjuncts of hab and hbc.
    -- We sketch the structure; the interesting disjuncts are muR on RHS
    -- and muUnfoldL on LHS.
    sorry

/-- The "true" subtyping relation is Sub at all step indices. -/
def Sub_si (Γ : Ctx) (a b : Expr) : Prop := ∀ k, SubN k Γ a b

namespace Sub_si

theorem refl (Γ : Ctx) (a : Expr) : Sub_si Γ a a := fun k => SubN.refl k Γ a

theorem top (Γ : Ctx) (a : Expr) : Sub_si Γ a .top := fun k => SubN.top k Γ a

theorem trans (Γ : Ctx) (a b c : Expr)
    (hab : Sub_si Γ a b) (hbc : Sub_si Γ b c) : Sub_si Γ a c :=
  fun k => SubN.trans k Γ a b c (hab k) (hbc k)

end Sub_si

/-- Inductive `Sub` embeds into `SubN` at every step index.
    This is the bridge from declarative subtyping to the step-indexed
    semantics. Once this holds, any derivation via `Sub` can be converted
    to a derivation via `SubN` (at any fuel), and the step-indexed
    transitivity can be used to discharge the `sorry`s in `Sub.trans`
    (by converting to SubN, composing, and converting back at the top
    level — though note that SubN → Sub is NOT proved, and does not hold
    in general; this bridge is one-way). -/
theorem Sub.toSubN : {Γ : Ctx} → {a b : Expr} → Sub Γ a b → (k : Nat) → SubN k Γ a b := by
  intro Γ a b h k
  cases k with
  | zero => trivial
  | succ k =>
    -- By induction on the Sub derivation. Each constructor maps to the
    -- corresponding SubBody disjunct. Recursive calls use SubN k via IH.
    sorry

/-- Derived: `Sub` entails `Sub_si`. -/
theorem Sub.toSub_si {Γ : Ctx} {a b : Expr} (h : Sub Γ a b) : Sub_si Γ a b :=
  Sub.toSubN h

end Och.Simple
