import Och.Simple.Syntax
import Och.Simple.Eval
import Och.Simple.Bidir

/-!
# Check-Primary Architecture (Phase 1)

## Architecture shift

Previously, soundness of Simple Och was formulated against the inductive
`Sub` relation:

    Sub Γ e τ → Compatible γ Γ → eval of closingSubst γ e and closingSubst γ τ
                                → Sub [] v_e v_τ

That is, the *declarative* `Sub` was the primary judgment, and the
algorithmic checker was meant to be shown sound against it.

In this file we flip the roles: **the bidirectional checker in
`Och.Simple.Bidir` is the type system**. The statement of soundness
becomes "check is preserved under evaluation":

    check Γ e τ = true → Compatible γ Γ →
      eval (closingSubst γ e) = some v_e →
      eval (closingSubst γ τ) = some v_τ →
      check [] v_e v_τ = true

### Why move away from the inductive `Sub`?

The inductive `Sub` can express Refl, Top, Var, Lam, App, Asc-L, Asc-R, Mu
(8 rules) but **cannot** directly express self-type introduction (the muR
rule we want): any attempt to add it produces a rule whose left and right
premises are not structurally smaller, breaking transitivity. We explored
this in the `research-*` branches.

Cycle detection in the *checker* handles this cleanly: the `seen` set plays
the role of a coinductive hypothesis. So we adopt the checker as primary.

### Roadmap

This is **Phase 1** of a multi-phase migration:

* **Phase 1 (this file)**: introduce `Compatible` on top of `check`, state
  the preservation-style soundness theorem, and discharge the trivial
  [Refl] and [Top] cases. Everything else is `sorry`ed.
* **Phase 2**: more base rules (Var, Lam, Asc-L, Asc-R).
* **Phase 3**: App (requires inversion on `check` for lambdas).
* **Phase 4**: Mu-L, and the key muR / cycle-detection case using a
  coinductive argument on the `seen` set.
* Eventually: delete the legacy inductive `Sub`, `Properties`, and
  `Soundness` files.

### Constraints during migration

* The inductive `Sub` in `Subtype.lean` stays at exactly 8 rules, zero
  sorrys. It remains the legacy formalization until we're confident in the
  check-primary approach.
* Any `sorry` in this file is deliberate and documented — all other
  modules must continue to build with zero sorrys.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

-- ============================================================
-- Closing substitution (copied from Soundness.lean)
--
-- We intentionally do NOT import Soundness.lean to keep CheckPrimary
-- independent of the legacy Sub-based machinery.
-- ============================================================

/-- Apply a list of closed values as a closing substitution.
    `γ = [v₀, v₁, …]` replaces `var 0 ↦ v₀`, `var 1 ↦ v₁`, …. -/
def closingSubst : List Expr → Expr → Expr
  | [], e => e
  | v :: rest, e => closingSubst rest (e.subst 0 v)

-- ============================================================
-- Compatible (γ ⊨ Γ) — check-based definition
-- ============================================================

/-- A closing substitution `γ` is *compatible* with context `Γ` when each
    value in `γ` check-types against its corresponding type in `Γ` at the
    **empty** context.

    NOTE: we check at `[]`, not at the remaining `Γ`, because by the time
    we consult a binding the earlier bindings have already been substituted
    away. Values therefore must already be closed (which the check at `[]`
    enforces structurally). -/
inductive Compatible : List Expr → Ctx → Prop where
  | nil : Compatible [] []
  | cons {v T : Expr} {γ : List Expr} {Γ : Ctx} :
      Compatible γ Γ →
      (∃ fuel, check fuel [] v T = true) →
      Compatible (v :: γ) (T :: Γ)

-- ============================================================
-- The new soundness theorem
-- ============================================================

/-- **Check-preservation soundness** (statement only, full proof deferred).

    If `Γ ⊢ e ⊑ τ` in the checker and `γ` is compatible with `Γ`, then
    after closing both `e` and `τ` and evaluating them, the resulting
    closed values still check-subtype at the empty context. -/
theorem soundness
    {Γ : Ctx} {e τ : Expr} {γ : List Expr}
    {fuel_check : Nat}
    (hcheck : check fuel_check Γ e τ = true)
    (hcompat : Compatible γ Γ)
    {fuel : Nat} {v_e v_τ : Expr}
    (he : eval fuel (closingSubst γ e) = some v_e)
    (hτ : eval fuel (closingSubst γ τ) = some v_τ) :
    ∃ fuel', check fuel' [] v_e v_τ = true := by
  -- The full proof is deferred to subsequent phases. We discharge only
  -- the very first cases below (Refl and Top) as a sanity check.
  sorry

-- ============================================================
-- Easy cases: direct-style lemmas
--
-- These are stand-alone lemmas that do NOT go through the full soundness
-- statement above; they are intended to show that the *computational*
-- architecture can dispatch the simple cases with zero effort, as
-- evidence that the approach is viable.
-- ============================================================

/-- Fuel monotonicity of `subCheck` (statement only, full proof deferred).
    Intuitively, giving the checker more fuel never turns a `true` into a
    `false`. Needed for the (∃ fuel, …) existentials to compose. -/
theorem subCheck_mono_fuel
    (fuel fuel' : Nat) (seen : List (Expr × Expr)) (Γ : Ctx) (a b : Expr)
    (h : subCheck fuel seen Γ a b = true) (hle : fuel ≤ fuel') :
    subCheck fuel' seen Γ a b = true := by
  sorry

/-- Fuel monotonicity of `check`. -/
theorem check_mono_fuel
    (fuel fuel' : Nat) (Γ : Ctx) (e τ : Expr)
    (h : check fuel Γ e τ = true) (hle : fuel ≤ fuel') :
    check fuel' Γ e τ = true := by
  sorry

/-- **Easy case: [Refl]-like.** `check` at fuel 2 accepts any reflexive
    pair in the empty context.

    The [Refl] branch at the top of `subCheck` fires because the `if decide
    (a = b)` guard is `true`, short-circuiting all subsequent matches. -/
theorem check_refl (v : Expr) : check 2 [] v v = true := by
  unfold check
  unfold subCheck
  simp

/-- **Easy case: [Top]-like.** `check` at fuel 2 accepts any LHS against
    `⊤` in the empty context.

    Either the [Refl] branch fires (if `v = .top`) or the outer `match b`
    on `.top` fires its first arm. Both return `true`. -/
theorem check_top (v : Expr) : check 2 [] v .top = true := by
  unfold check
  unfold subCheck
  by_cases h : v = .top
  · subst h; simp
  · simp [h]

end Och.Simple
