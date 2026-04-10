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
  intro k
  induction k with
  | zero => intro _ _ _ _; trivial
  | succ k ih =>
    intro Γ a b h
    -- h : SubN (k+2) Γ a b, i.e. SubBody (SubN (k+1)) Γ a b
    -- goal : SubN (k+1) Γ a b, i.e. SubBody (SubN k) Γ a b
    show SubBody (SubN k) Γ a b
    rcases h with heq | htop | ⟨x, T, hax, hget, hTb⟩
      | ⟨A₁, b₁, A₂, b₂, hax, hbx, hA, hb⟩
      | ⟨f, a', D, Rl, hax, hfD, haD, hR⟩
      | ⟨e, τ, hax, heτ, hτb⟩
      | ⟨e, τ, hbx, heτ, hae⟩
      | ⟨A, body, hax, hAb, hbody⟩
      | ⟨A, body, hax, hbody, hunfold⟩
      | ⟨A, body, hbx, haA, haBody⟩
    · left; exact heq
    · right; left; exact htop
    · right; right; left
      exact ⟨x, T, hax, hget, ih Γ T b hTb⟩
    · right; right; right; left
      exact ⟨A₁, b₁, A₂, b₂, hax, hbx, ih Γ A₂ A₁ hA, ih (A₂ :: Γ) b₁ b₂ hb⟩
    · right; right; right; right; left
      exact ⟨f, a', D, Rl, hax, ih Γ f (.lam D Rl) hfD, ih Γ a' D haD, ih Γ (Rl.subst 0 a') b hR⟩
    · right; right; right; right; right; left
      exact ⟨e, τ, hax, ih Γ e τ heτ, ih Γ τ b hτb⟩
    · right; right; right; right; right; right; left
      exact ⟨e, τ, hbx, ih Γ e τ heτ, ih Γ a e hae⟩
    · right; right; right; right; right; right; right; left
      exact ⟨A, body, hax, ih Γ A b hAb, ih (A :: Γ) body (A.shift 0 1) hbody⟩
    · right; right; right; right; right; right; right; right; left
      exact ⟨A, body, hax, ih (A :: Γ) body (A.shift 0 1) hbody, ih Γ (body.subst 0 (.mu A body)) b hunfold⟩
    · right; right; right; right; right; right; right; right; right
      exact ⟨A, body, hbx, ih Γ a A haA, ih Γ a (body.subst 0 a) haBody⟩

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

/-- Transitivity of SubN.

    **Status**: genuinely blocked in its most general form. See the detailed
    note below. Concentrating all the remaining difficulty into this single
    `sorry` is the point of this file — Properties.lean's transitivity sorrys
    can then be discharged by `Sub.toSubN` / `SubN.trans` / (back to Sub),
    provided the downstream conversion holds.

    **Why this is hard**: By induction on `k`, the induction step reduces to
    composing SubBody disjuncts. For most disjunct pairings this is routine.
    The obstacle is the muR-on-RHS case:
      `hab : SubN (k+1) Γ a b'` and
      `hbc : SubN (k+1) Γ b' (μA.body)` via muR, decomposing to
        `SubN k Γ b' A` and `SubN k Γ b' (body[0:=b'])`.
    Goal `SubN (k+1) Γ a (μA.body)` via muR requires both
      `SubN k Γ a A` (OK: composes via IH) and
      `SubN k Γ a (body[0:=a])` (HARD).
    The latter requires replacing `b'` with `a` inside `body[0:=·]`. This is
    a substitution compatibility lemma, which is FALSE in general because
    `body` may use its self-reference (var 0) contravariantly. Concretely, if
    `body = .lam (.var 0) .top`, then `body[0:=a] = .lam a .top` and
    `body[0:=b'] = .lam b' .top`; the lam rule requires `b' ⊑ a` for the
    contravariant domain, which we only have as `a ⊑ b'`.

    The Fu-Stump (2014) metatheory handles expressive self-types via erasure
    to System Fω, NOT via step-indexing. The step-indexed approach of Ahmed
    (2006) handles only the WEAK form of muR (self = μA.b). Closing this
    sorry requires either (a) an erasure/semantic argument, (b) a stronger
    syntactic restriction on the bodies of μ types that arise in practice, or
    (c) a different SubN definition (e.g., coinductive bisimulation via
    Iris-in-Lean). -/
theorem SubN.trans : (k : Nat) → (Γ : Ctx) → (a b c : Expr) →
    SubN k Γ a b → SubN k Γ b c → SubN k Γ a c := by
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
  intro Γ a b h
  induction h with
  | refl Γ a =>
    intro k; cases k with
    | zero => trivial
    | succ k => show SubBody (SubN k) Γ a a; left; rfl
  | top Γ a =>
    intro k; cases k with
    | zero => trivial
    | succ k => show SubBody (SubN k) Γ a .top; right; left; rfl
  | var Γ x b T hget _ ih =>
    intro k; cases k with
    | zero => trivial
    | succ k =>
      show SubBody (SubN k) Γ (.var x) b
      right; right; left
      exact ⟨x, T, rfl, hget, ih k⟩
  | lam Γ A B b₁ b₂ _ _ ihBA ihbody =>
    intro k; cases k with
    | zero => trivial
    | succ k =>
      show SubBody (SubN k) Γ (.lam A b₁) (.lam B b₂)
      right; right; right; left
      exact ⟨A, b₁, B, b₂, rfl, rfl, ihBA k, ihbody k⟩
  | app Γ f a b D R _ _ _ ihfD ihaD ihRb =>
    intro k; cases k with
    | zero => trivial
    | succ k =>
      show SubBody (SubN k) Γ (.app f a) b
      right; right; right; right; left
      exact ⟨f, a, D, R, rfl, ihfD k, ihaD k, ihRb k⟩
  | ascL Γ e τ b _ _ iheτ ihτb =>
    intro k; cases k with
    | zero => trivial
    | succ k =>
      show SubBody (SubN k) Γ (.asc e τ) b
      right; right; right; right; right; left
      exact ⟨e, τ, rfl, iheτ k, ihτb k⟩
  | ascR Γ a e τ _ _ iheτ ihae =>
    intro k; cases k with
    | zero => trivial
    | succ k =>
      show SubBody (SubN k) Γ a (.asc e τ)
      right; right; right; right; right; right; left
      exact ⟨e, τ, rfl, iheτ k, ihae k⟩
  | mu Γ A body c _ _ ihAc ihbodyA =>
    intro k; cases k with
    | zero => trivial
    | succ k =>
      show SubBody (SubN k) Γ (.mu A body) c
      right; right; right; right; right; right; right; left
      exact ⟨A, body, rfl, ihAc k, ihbodyA k⟩
  | muR Γ a A body _ _ ihaA ihaBody =>
    intro k; cases k with
    | zero => trivial
    | succ k =>
      show SubBody (SubN k) Γ a (.mu A body)
      right; right; right; right; right; right; right; right; right
      exact ⟨A, body, rfl, ihaA k, ihaBody k⟩
  | muUnfoldL Γ A body c _ _ ihbA ihunfold =>
    intro k; cases k with
    | zero => trivial
    | succ k =>
      show SubBody (SubN k) Γ (.mu A body) c
      right; right; right; right; right; right; right; right; left
      exact ⟨A, body, rfl, ihbA k, ihunfold k⟩

/-- Derived: `Sub` entails `Sub_si`. -/
theorem Sub.toSub_si {Γ : Ctx} {a b : Expr} (h : Sub Γ a b) : Sub_si Γ a b :=
  Sub.toSubN h

/-- **BRIDGE** (companion sorry): convert a step-indexed witness back to an
    inductive `Sub` derivation.

    In the step-indexed subtyping literature, this direction is typically NOT
    provable in general (step-indexed logical relations are sound but not
    complete w.r.t. syntactic subtyping). The challenge is that SubN is
    Prop-valued and lossy — it encodes existence of a structural path but
    does not retain enough data to reconstruct a `Sub` derivation tree.

    **Status**: companion sorry to `SubN.trans`. Together these two sorries
    concentrate the remaining metatheoretic load: closing either (a) `SubN.trans`
    with a substitution compatibility argument, or (b) `SubN.toSub` with a
    proof-relevant version of SubN, would discharge the 7 transitivity / eval
    preservation sorries that otherwise pollute Properties.lean and
    Soundness.lean.

    The parameter `k : Nat` and hypothesis are here for flexibility; the
    actual proof (when unblocked) may need `k` large, or need SubN redefined
    as `Type` rather than `Prop`. -/
noncomputable def SubN.toSub {Γ : Ctx} {a b : Expr} (k : Nat)
    (_hk : k ≥ 1) (h : SubN k Γ a b) : Sub Γ a b := by
  sorry

end Och.Simple
