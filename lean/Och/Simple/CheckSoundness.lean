import Och.Simple.Check
import Och.Simple.Soundness

/-!
# Soundness of the constructive checker w.r.t. eval

This module ties the bidirectional checker (`subCheck` in `Check.lean`) to
the concrete semantics (`eval` in `Eval.lean`) via the already-established
inductive `Sub` relation.

## Strategy (option B from the research brief)

1. `subCheck_sound` (proven in `Check.lean`):
     `subCheck fuel Γ a b = true → Sub Γ a b`
2. `semanticSubst` (proven in `Soundness.lean`):
     `Sub Γ e τ → Compatible γ Γ → Sub [] (closingSubst γ e) (closingSubst γ τ)`
3. `evalPreservation` (proven in `Soundness.lean`):
     `Sub [] e τ → eval e = some v_e → eval τ = some v_τ → Sub [] v_e v_τ`

Composing these three gives full soundness of `check` with respect to `eval`:
if the checker accepts `e ⊑ τ` in context `Γ`, and a compatible closing
substitution `γ` reduces both to values `v_e`, `v_τ`, then `v_e ⊑ v_τ`
holds in the empty context.
-/

set_option autoImplicit false

namespace Och.Simple

open Expr

-- ============================================================
-- Compatibility (checker-indexed variant)
-- ============================================================

/-- A closing substitution `γ` is checker-compatible with context `Γ` if each
    value is accepted by the checker (at its type, in the remaining context).

    This is the bool-valued analogue of `Compatible` from `Soundness.lean`;
    `Compatible_of_CheckCompat` below converts one into the other via
    `subCheck_sound`. -/
inductive CheckCompat : (fuel : Nat) → List Expr → Ctx → Type where
  | nil (fuel : Nat) : CheckCompat fuel [] []
  | cons {fuel : Nat} {v T : Expr} {γ : List Expr} {Γ : Ctx} :
      CheckCompat fuel γ Γ →
      subCheck fuel [] Γ v T = true →
      CheckCompat fuel (v :: γ) (T :: Γ)

-- ============================================================
-- Converting check compatibility → Sub compatibility
-- ============================================================

/-- Empty `seen` is always justified (vacuous). -/
private def emptySeenJustified (Γ : Ctx) : SeenJustified [] Γ :=
  fun _ hp => by simp [seenMem] at hp

/-- Every checker-compatible environment is also `Compatible` in the Sub sense. -/
noncomputable def Compatible_of_CheckCompat :
    {fuel : Nat} → {γ : List Expr} → {Γ : Ctx} →
    CheckCompat fuel γ Γ → Compatible γ Γ
  | _, _, _, .nil _ => Compatible.nil
  | _, _, _, .cons hrest hv =>
    Compatible.cons (Compatible_of_CheckCompat hrest)
      (subCheck_sound _ _ _ _ _ (emptySeenJustified _) hv)

-- ============================================================
-- Main soundness theorem
-- ============================================================

/-- **Check soundness w.r.t. eval (Sub-level statement)**.

    If the checker accepts `Γ ⊢ e ⊑ τ`, the closing substitution `γ` is
    checker-compatible with `Γ`, and both `closingSubst γ e` and
    `closingSubst γ τ` reduce under the concrete evaluator to values
    `v_e` and `v_τ`, then `Sub [] v_e v_τ` holds.

    The conclusion is expressed at the inductive `Sub` level because that is
    what composition through the existing soundness infrastructure directly
    gives us. A Bool-level corollary can be derived via completeness when
    needed (out of scope for this baseline). -/
noncomputable def soundness_sub
    {fuel_chk : Nat} {Γ : Ctx} {e τ : Expr} {γ : List Expr}
    (hcheck : subCheck fuel_chk [] Γ e τ = true)
    (hcompat : CheckCompat fuel_chk γ Γ)
    {fuel_e fuel_τ : Nat} {v_e v_τ : Expr}
    (he : eval fuel_e (closingSubst γ e) = some v_e)
    (hτ : eval fuel_τ (closingSubst γ τ) = some v_τ)
    : Sub [] v_e v_τ :=
  let hsub : Sub Γ e τ := subCheck_sound fuel_chk [] Γ e τ (emptySeenJustified _) hcheck
  let hcompat' : Compatible γ Γ := Compatible_of_CheckCompat hcompat
  let hsub_closed : Sub [] (closingSubst γ e) (closingSubst γ τ) :=
    semanticSubst hsub hcompat'
  evalPreservation hsub_closed fuel_e fuel_τ v_e v_τ he hτ

-- ============================================================
-- Alias matching the canonical `check` name from the brief
-- ============================================================

/-- **Check soundness (using `check`)**. Re-exposes `soundness_sub` under the
    top-level `check` name. -/
noncomputable def check_sound
    {fuel_chk : Nat} {Γ : Ctx} {e τ : Expr} {γ : List Expr}
    (hcheck : check fuel_chk Γ e τ = true)
    (hcompat : CheckCompat fuel_chk γ Γ)
    {fuel_e fuel_τ : Nat} {v_e v_τ : Expr}
    (he : eval fuel_e (closingSubst γ e) = some v_e)
    (hτ : eval fuel_τ (closingSubst γ τ) = some v_τ)
    : Sub [] v_e v_τ :=
  soundness_sub hcheck hcompat he hτ

end Och.Simple
