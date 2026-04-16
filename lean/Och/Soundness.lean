import Och.Syntax
import Och.Eval
import Och.Subtyping

/-!
# Soundness via Logical Relations (VCompat)

## Goal

Prove: if `absEval` succeeds, `concEval(e)` is compatible with `absEval(e)`.

## Status

Sorryed out during bidirectional refactor. VCompat definition and key theorem
signatures preserved for future re-proving.
-/

open Expr

/-! ## VCompat: step-indexed value-type compatibility -/

/-- Step-indexed value-type compatibility. VCompat n v τ means the concrete
    value v is compatible with the abstract type τ for n observation steps. -/
def VCompat : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | n + 1, v, τ =>
    τ = .type
    ∨ v = τ
    ∨ (∃ domV domT bodyV bodyT,
        v = .lam domV bodyV ∧ τ = .lam domT bodyT ∧
        ∀ (j : Nat), j ≤ n → ∀ (aV aT : Expr),
          ConcNF aV →
          VCompat j aV aT →
          aT.closedAt 0 = true →
          ∀ (fuel : Nat) rv, concEval fuel (bodyV.subst 0 aV) = some rv →
          VCompat j rv (bodyT.subst 0 aT))
    ∨ (∃ annV annT bodyV bodyT,
        v = .iota annV bodyV ∧ τ = .iota annT bodyT ∧
        VCompat n (bodyV.subst 0 (.iota annV bodyV)) (bodyT.subst 0 (.iota annV bodyV)))
    ∨ (∃ annV annT bodyV bodyT,
        v = .fix annV bodyV ∧ τ = .fix annT bodyT ∧
        VCompat n (bodyV.subst 0 (.fix annV bodyV)) (bodyT.subst 0 (.fix annV bodyV)))
    ∨ (∃ ann body,
        τ = .iota ann body ∧
        VCompat n v (body.subst 0 v))
    ∨ (∃ ann body,
        τ = .fix ann body ∧
        VCompat n v (body.subst 0 (.fix ann body)))
    ∨ (∃ ann body, ∃ (nfuel : Nat) (nctx : TyCtx) (nseen : List (Expr × Expr)) (u' : NfExpr × NfExpr),
        τ = .iota ann body ∧
        absEval nfuel nctx nseen (body.subst 0 v) = .ok u' ∧
        VCompat n v u'.1.val)
    ∨ (∃ ann body,
        v = .iota ann body ∧
        VCompat n (body.subst 0 (.iota ann body)) τ)
    ∨ (∃ ann body,
        v = .fix ann body ∧
        VCompat n (body.subst 0 (.fix ann body)) τ)
    ∨ (∃ fV fT aV aT,
        v = .app fV aV ∧ τ = .app fT aT ∧
        VCompat n fV fT ∧ VCompat n aV aT)
    -- Context type lookup: for neutral terms, look up type in context
    ∨ (∃ (ctx : TyCtx) (k : Nat) (ty : NfExpr),
        v = .bvar k ∧ ctx.get? k = some ty ∧ VCompat n ty.val τ)
    ∨ (∃ term tyAsc, v = .asc term tyAsc ∧ VCompat n term τ)

@[simp] theorem VCompat.zero_eq (v τ : Expr) : VCompat 0 v τ = True := by
  unfold VCompat; rfl

/-! ## Key theorems (sorryed — to be re-proved) -/

theorem VCompat.mono {n : Nat} {v τ : Expr}
    (h : VCompat (n + 1) v τ) : VCompat n v τ := by sorry

theorem VCompat.refl (n : Nat) (e : Expr) : VCompat n e e := by sorry

/-- Main soundness theorem: if absEval and concEval both succeed on a closed term,
    their results are compatible. -/
theorem soundness
    {fuel : Nat} {e v : Expr} {τ : NfExpr × NfExpr}
    (h_abs : absEval fuel [] [] e = .ok τ)
    (h_conc : concEval fuel e = some v)
    (h_closed : e.closedAt 0 = true)
    : ∀ n, VCompat n v τ.1.val := by sorry
